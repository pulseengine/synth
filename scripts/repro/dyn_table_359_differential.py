import struct,sys
from elftools.elf.elffile import ELFFile
from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB
from unicorn.arm_const import *
import sys
ELF=sys.argv[1] if len(sys.argv)>1 else "/tmp/dt.o"; CODE,DATA,STK=0x1000000,0x3000000,0x6000000; RET=CODE+0xFFF0
e=ELFFile(open(ELF,"rb")); text=bytearray(e.get_section_by_name(".text").data())
st=[s for s in e.iter_sections() if s["sh_type"]=="SHT_SYMTAB"][0]
syms={s.name:s["st_value"] for s in st.iter_symbols()}
# section addrs: place .data (seg) at a known spot; resolve __synth_wasm_seg_0 to it
secaddr={}; cur=DATA
for sec in e.iter_sections():
    if sec["sh_flags"]&0x2 and sec.name in('.bss','.data'):  # ALLOC
        secaddr[sec.name]=cur; cur+=max(sec["sh_size"],0x1000)
data_sec=e.get_section_by_name(".data"); data_bytes=bytearray(data_sec.data()) if data_sec else bytearray()
# symbol runtime addr = its section base + value
secbyidx={i:s.name for i,s in enumerate(e.iter_sections())}
def symaddr(name):
    s=[x for x in st.iter_symbols() if x.name==name][0]
    return secaddr.get(secbyidx[s["st_shndx"]],DATA)+s["st_value"]
for r in e.get_section_by_name(".rel.text").iter_relocations():
    if r["r_info_type"]==2:
        sym=st.get_symbol(r["r_info_sym"]); (add,)=struct.unpack_from("<I",text,r["r_offset"])
        struct.pack_into("<I",text,r["r_offset"],(symaddr(sym.name)+add)&0xFFFFFFFF)
mu=Uc(UC_ARCH_ARM,UC_MODE_THUMB)
mu.mem_map(CODE,0x100000); mu.mem_map(DATA,0x400000); mu.mem_map(STK,0x100000)
mu.mem_write(CODE,bytes(text))
if '.data' in secaddr: mu.mem_write(secaddr['.data'],bytes(data_bytes))
mu.mem_write(RET,b"\x00\xbf\x00\xbf")
ok=0
for i,exp in [(0,10),(1,20),(2,30),(3,40)]:
    mu.reg_write(UC_ARM_REG_R0,i); mu.reg_write(UC_ARM_REG_R11,0); mu.reg_write(UC_ARM_REG_SP,STK+0x80000); mu.reg_write(UC_ARM_REG_LR,RET|1)
    mu.emu_start((CODE+(syms["lookup"]&~1))|1,RET,count=2000)
    got=mu.reg_read(UC_ARM_REG_R0)&0xFFFFFFFF; ok+=(got==exp)
    print(f"lookup({i})={got} (expect {exp}) {'OK' if got==exp else 'BUG'}")
print("ORACLE: PASS" if ok==4 else "ORACLE: FAIL"); sys.exit(0 if ok==4 else 1)
