import struct, sys
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import *
import sys
ELF=sys.argv[1] if len(sys.argv)>1 else "/tmp/sret.o"; CODE,DATA,STK=0x1000000,0x3000000,0x6000000; RET=CODE+0xFFF0
e=ELFFile(open(ELF,"rb")); text=bytearray(e.get_section_by_name(".text").data())
ds=e.get_section_by_name(".data"); data=bytearray(ds.data()) if ds else bytearray(0x10000)
st=[s for s in e.iter_sections() if s["sh_type"]=="SHT_SYMTAB"][0]
syms={s.name:s["st_value"] for s in st.iter_symbols()}
def bl(pc,t):
    o=(t-(pc+4))&0x1FFFFFF;s=(o>>24)&1;i1=(o>>23)&1;i2=(o>>22)&1
    im10=(o>>12)&0x3FF;im11=(o>>1)&0x7FF;j1=(~i1&1)^s;j2=(~i2&1)^s
    return 0xF000|(s<<10)|im10,0xD000|(j1<<13)|(j2<<11)|im11
for r in e.get_section_by_name(".rel.text").iter_relocations():
    t=r["r_info_type"]; off=r["r_offset"]; sym=st.get_symbol(r["r_info_sym"])
    if t in (10,30):
        tgt=CODE+(syms[sym.name]&~1); h1,h2=bl(CODE+off,tgt); struct.pack_into("<HH",text,off,h1,h2)
    elif t==2:  # R_ARM_ABS32
        (add,)=struct.unpack_from("<I",text,off)
        struct.pack_into("<I",text,off,(DATA+syms[sym.name]+add)&0xFFFFFFFF)
mu=Uc(UC_ARCH_ARM,UC_MODE_THUMB)
mu.mem_map(CODE,0x100000); mu.mem_map(DATA,0x200000); mu.mem_map(STK,0x100000)
mu.mem_write(CODE,bytes(text)); mu.mem_write(DATA,bytes(data)); mu.mem_write(RET,b"\x00\xbf\x00\xbf")
def run(w,u,m):
    mu.reg_write(UC_ARM_REG_R0,w); mu.reg_write(UC_ARM_REG_R1,u); mu.reg_write(UC_ARM_REG_R2,m)
    mu.reg_write(UC_ARM_REG_R11,DATA); mu.reg_write(UC_ARM_REG_SP,STK+0x80000); mu.reg_write(UC_ARM_REG_LR,RET|1)
    mu.emu_start((CODE+(syms["shim"]&~1))|1,RET,timeout=5_000_000,count=20000)
    return struct.unpack("<i",struct.pack("<I",mu.reg_read(UC_ARM_REG_R0)&0xFFFFFFFF))[0]
for (w,u,m,exp) in [(0,0,8,0),(3,8,8,-35),(0,2,8,0)]:
    got=run(w,u,m); print(f"shim(write_idx={w},used={u},max={m}) = {got}  (expect {exp})  {'OK' if got==exp else 'MISMATCH <-- BUG'}")
