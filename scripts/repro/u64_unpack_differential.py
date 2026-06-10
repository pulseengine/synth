import struct, sys
import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R11,
                               UC_ARM_REG_LR, UC_ARM_REG_SP)

# ground truth
eng = wasmtime.Engine(); mod = wasmtime.Module(eng, open('/tmp/u64repro.wat','rb').read())
st = wasmtime.Store(eng); inst = wasmtime.Instance(st, mod, [])
gt = {n: inst.exports(st)[n] for n in ("check","check_call")}

e = ELFFile(open('/tmp/u64.elf','rb'))
text = bytearray(e.get_section_by_name('.text').data())
symtab = [s for s in e.iter_sections() if s['sh_type']=='SHT_SYMTAB'][0]
syms = {s.name: s['st_value'] for s in symtab.iter_symbols()}
# resolve internal BL relocs (R_ARM_THM_CALL=10)
rel = e.get_section_by_name('.rel.text')
if rel:
    for r in rel.iter_relocations():
        if r['r_info_type'] == 10:
            s = symtab.get_symbol(r['r_info_sym'])
            if s.name in syms:
                off, target = r['r_offset'], syms[s.name]
                pc = off + 4
                d = (target - pc) & 0xFFFFFFFF
                # encode Thumb BL imm
                dd = (target - pc)
                S_ = (dd >> 24) & 1
                i1 = (dd >> 23) & 1; i2 = (dd >> 22) & 1
                j1 = (~(i1 ^ S_)) & 1; j2 = (~(i2 ^ S_)) & 1
                imm10 = (dd >> 12) & 0x3FF; imm11 = (dd >> 1) & 0x7FF
                hw1 = 0xF000 | (S_ << 10) | imm10
                hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
                struct.pack_into('<HH', text, off, hw1, hw2)

CODE, STK = 0x10000, 0x90000
mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
mu.mem_map(CODE, 0x10000); mu.mem_write(CODE, bytes(text))
mu.mem_map(STK, 0x10000)
RET = CODE + 0xFF00
mu.mem_write(RET, b"\x00\xbf\x00\xbf")

ok = True
for fn in ("check","check_call"):
    for (a,b) in ((3,4),(0,0),(250,5),(0x7FFFFFFF,1)):
        exp = gt[fn](st, a, b) & 0xFFFFFFFF
        mu.reg_write(UC_ARM_REG_R0, a); mu.reg_write(UC_ARM_REG_R1, b)
        mu.reg_write(UC_ARM_REG_R11, 0); mu.reg_write(UC_ARM_REG_SP, STK+0x8000)
        mu.reg_write(UC_ARM_REG_LR, RET|1)
        mu.emu_start((CODE+syms[fn])|1, RET, timeout=5_000_000)
        got = mu.reg_read(UC_ARM_REG_R0)
        m = "OK " if got==exp else "FAIL"
        if got!=exp: ok=False
        print(f"{m} {fn}({a},{b}) = {got:#x} expect {exp:#x}")
print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
