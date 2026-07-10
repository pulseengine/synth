from unicorn import *
from unicorn.arm_const import *
code=open('/tmp/gz.bin','rb').read()
CODE=0x10000;STACK=0x20000;LIN=0x40000;SZ=0x10000
mu=Uc(UC_ARCH_ARM,UC_MODE_THUMB)
for b in (CODE,STACK,LIN): mu.mem_map(b,SZ)
mu.mem_write(CODE,code)
SEM=0x100
mu.mem_write(LIN+SEM,(0).to_bytes(4,'little')); mu.mem_write(LIN+SEM+4,(1).to_bytes(4,'little'))
mu.reg_write(UC_ARM_REG_SP,STACK+0x8000); mu.reg_write(UC_ARM_REG_R11,LIN); mu.reg_write(UC_ARM_REG_R0,SEM)
RET=0x15000; mu.reg_write(UC_ARM_REG_LR,RET|1)
# fresh reloc offsets (from `synth disasm`): stub all imports; the no-waiter
# path is z_unpend_first_thread (0xbc) returning 0.
STUBS={0xac:0,0xbc:0,0x1c0:0,0x1d8:0,0x214:0}
def codeh(mu,addr,size,u):
    off=addr-CODE
    if off in STUBS: mu.reg_write(UC_ARM_REG_R0,STUBS[off]); mu.reg_write(UC_ARM_REG_PC,(addr+4)|1)
def memh(mu,t,addr,size,val,u):
    if LIN+SEM<=addr<LIN+SEM+16: print(f'  STORE count-region linmem[sem+{addr-LIN-SEM}] = {val}')
mu.hook_add(UC_HOOK_CODE,codeh); mu.hook_add(UC_HOOK_MEM_WRITE,memh)
ZIMPL=CODE+0x98
try: mu.emu_start(ZIMPL|1,RET,count=3000)
except UcError as e: print('emu stop:',e,'pc=%#x'%mu.reg_read(UC_ARM_REG_PC))
count=int.from_bytes(mu.mem_read(LIN+SEM,4),'little')
print(f"AFTER give: sem->count = {count}")
print("VERDICT:", "FIXED (count=1)" if count==1 else f"STILL WRONG (count={count})")
