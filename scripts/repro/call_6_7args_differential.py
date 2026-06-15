import struct, sys
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import *
ELF=sys.argv[1] if len(sys.argv)>1 else "/tmp/cm.o"; CODE,DATA,STK=0x10000,0x40000,0x90000; RET=CODE+0x4000
e=ELFFile(open(ELF,"rb")); text=bytearray(e.get_section_by_name(".text").data())
st=[s for s in e.iter_sections() if s["sh_type"]=="SHT_SYMTAB"][0]
syms={s.name:s["st_value"] for s in st.iter_symbols()}
def bl(pc,t):
    o=(t-(pc+4))&0x1FFFFFF; s=(o>>24)&1;i1=(o>>23)&1;i2=(o>>22)&1
    im10=(o>>12)&0x3FF;im11=(o>>1)&0x7FF;j1=(~i1&1)^s;j2=(~i2&1)^s
    return 0xF000|(s<<10)|im10, 0xD000|(j1<<13)|(j2<<11)|im11
for r in e.get_section_by_name(".rel.text").iter_relocations():
    if r["r_info_type"] in (10,30):
        sym=st.get_symbol(r["r_info_sym"]); tgt=CODE+(syms[sym.name]&~1); off=r["r_offset"]
        h1,h2=bl(CODE+off,tgt); struct.pack_into("<HH",text,off,h1,h2)
def run(entry, args):
    uc=Uc(UC_ARCH_ARM,UC_MODE_THUMB)
    for b in (CODE,DATA,STK): uc.mem_map(b,0x10000)
    uc.mem_write(CODE,bytes(text)); sp=STK+0x8000
    stackargs=args[4:]  # params 4+ on incoming stack
    sp-=((len(stackargs)*4+7)&~7) if stackargs else 0
    for k,v in enumerate(stackargs): uc.mem_write(sp+k*4, struct.pack("<I",v&0xFFFFFFFF))
    uc.reg_write(UC_ARM_REG_SP,sp)
    for k,reg in enumerate([UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3]):
        if k<len(args): uc.reg_write(reg,args[k]&0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R11,DATA); uc.reg_write(UC_ARM_REG_LR,RET|1)
    uc.emu_start((CODE+(syms[entry]&~1))|1, RET, count=4000)
    return uc.reg_read(UC_ARM_REG_R0)&0xFFFFFFFF
ok=0;tot=0
for (entry,args) in [("call6",(1,2,3,4,5,6)),("call6",(15,0,0,0,0,9)),("call7",(1,2,3,4,5,6,7)),("call7",(0,0,0,0,0,0,15))]:
    exp=0
    for k,v in enumerate(args): exp|=(v&0xF)<<(4*k)
    exp&=0xFFFFFFFF; got=run(entry,list(args)); tot+=1
    f="OK" if got==exp else "MISMATCH"; ok+=(got==exp)
    print(f"{entry}{args} = 0x{got:07X} (expect 0x{exp:07X}) {f}")
print(f"\n{ok}/{tot} match"); print("ORACLE: PASS" if ok==tot else "ORACLE: FAIL")
sys.exit(0 if ok==tot else 1)
