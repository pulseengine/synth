import sys
import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_RISCV, UC_MODE_RISCV32
from unicorn.riscv_const import (UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_RA,
                                 UC_RISCV_REG_SP)
eng = wasmtime.Engine(); mod = wasmtime.Module(eng, open('scripts/repro/u64_unpack_inlined.wat','rb').read())
st = wasmtime.Store(eng); inst = wasmtime.Instance(st, mod, [])
gt = inst.exports(st)["check"]
e = ELFFile(open('/tmp/u64_rv32.elf','rb'))
text = e.get_section_by_name('.text').data()
symtab = [s for s in e.iter_sections() if s['sh_type']=='SHT_SYMTAB'][0]
syms = {s.name: s['st_value'] for s in symtab.iter_symbols()}
CODE, STK = 0x10000, 0x90000
mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
mu.mem_map(CODE, 0x10000); mu.mem_write(CODE, text); mu.mem_map(STK, 0x10000)
RET = CODE + 0xFF00
mu.mem_write(RET, b"\x13\x00\x00\x00")  # nop pad (mapped RA target, #220 gotcha)
ok = True
for (a,b) in ((3,4),(0,0),(250,5),(0x7FFFFFFF,1)):
    exp = gt(st, a, b) & 0xFFFFFFFF
    mu.reg_write(UC_RISCV_REG_A0, a); mu.reg_write(UC_RISCV_REG_A1, b)
    mu.reg_write(UC_RISCV_REG_SP, STK + 0x8000); mu.reg_write(UC_RISCV_REG_RA, RET)
    mu.emu_start(CODE + syms["check"], RET, timeout=5_000_000)
    got = mu.reg_read(UC_RISCV_REG_A0)
    print(f'{"OK " if got==exp else "FAIL"} check({a},{b}) = {got:#x} expect {exp:#x}')
    ok &= got == exp
print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
