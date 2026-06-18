# Does ld64(addr) read mem[addr] (correct) or mem[0] (address dropped)?
import subprocess
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_SP,UC_ARM_REG_LR,UC_ARM_REG_R11,UC_ARM_REG_PC
from elftools.elf.elffile import ELFFile
ELF="/tmp/i64/i64_d.elf"
nm=subprocess.run(["arm-none-eabi-nm",ELF],capture_output=True,text=True).stdout
entry=next(int(l.split()[0],16) for l in nm.splitlines() if l.endswith(" T ld64"))
with open(ELF,'rb') as fh:
    elf=ELFFile(fh); t=elf.get_section_by_name('.text'); tb,td=t['sh_addr'],t.data()
uc=Uc(UC_ARCH_ARM,UC_MODE_THUMB); uc.mem_map(0,0x10000); uc.mem_write(tb,td)
LIN=0x20000000; uc.mem_map(LIN,0x10000); uc.reg_write(UC_ARM_REG_R11,LIN)
# distinct 8-byte values at offset 0 and offset 16
uc.mem_write(LIN+0,  b'\xAA'*8)
uc.mem_write(LIN+16, b'\x11\x22\x33\x44\x55\x66\x77\x88')
SP=LIN+0x8000; uc.reg_write(UC_ARM_REG_SP,SP)
PAD=0x300000; uc.mem_map(PAD,0x1000); uc.reg_write(UC_ARM_REG_LR,PAD|1)
uc.reg_write(UC_ARM_REG_R0,16)  # address param = 16
uc.emu_start(entry|1,PAD,count=50)
lo=uc.reg_read(UC_ARM_REG_R0)&0xFFFFFFFF; hi=uc.reg_read(UC_ARM_REG_R1)&0xFFFFFFFF
got=(hi<<32)|lo
print(f"ld64(16) = {got:#018x}")
print(f"  mem[16] = 0x8877665544332211 (CORRECT)" )
print(f"  mem[0]  = 0xaaaaaaaaaaaaaaaa (address dropped)")
print("VERDICT:", "CORRECT (uses addr)" if got==0x8877665544332211 else ("ADDRESS DROPPED" if got==0xaaaaaaaaaaaaaaaa else f"OTHER {got:#x}"))
