# #594: call_indirect on the A32 path (--target cortex-r5) compiled to a NOP —
# no call, wrong result (leftover table index instead of the callee's return).
#
# Differential: emulate the A32 object under unicorn (UC_MODE_ARM, not THUMB)
# against the wasmtime oracle (run() = 42).
#
# ArmOp::CallIndirect contract (same as the Thumb-2 path): R11 holds the
# function-pointer table base; entry i is a 4-byte code address. The harness
# builds that table with func_0's address (bit 0 clear — A32) and sets R11.
#
# Usage: python3 call_indirect_594_differential.py <elf>
#   <elf> = synth compile call_indirect_594.wat --target cortex-r5 \
#             --all-exports --relocatable --no-optimize -o <elf>
import struct
import sys

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_ARM
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/ci594.o"
CODE, TABLE, STK = 0x1000000, 0x3000000, 0x6000000
RET = CODE + 0xFFF0
EXPECT = 42  # wasmtime --invoke run call_indirect_594.wat

e = ELFFile(open(ELF, "rb"))
text = bytearray(e.get_section_by_name(".text").data())
# Symbols from the symtab, never from disasm text (host-dependent).
# NOTE: the ELF builder currently sets the Thumb interworking bit on every
# STT_FUNC symbol even for A32 targets (pre-existing defect, noted on #594) —
# mask bit 0 to get the real A32 code address.
st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
for need in ("run", "func_0"):
    if need not in syms:
        print(f"SYMBOL MISSING: {need}")
        sys.exit(1)

mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)
mu.mem_map(CODE, 0x100000)
mu.mem_map(TABLE, 0x10000)
mu.mem_map(STK, 0x100000)
mu.mem_write(CODE, bytes(text))
# table[0] = address of func_0 (A32: bit 0 clear)
mu.mem_write(TABLE, struct.pack("<I", CODE + syms["func_0"]))
# Return pad: A32 NOPs at RET (mapped inside the CODE region).
mu.mem_write(RET, struct.pack("<II", 0xE1A00000, 0xE1A00000))

mu.reg_write(UC_ARM_REG_R11, TABLE)
mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
mu.reg_write(UC_ARM_REG_LR, RET)  # A32 return address: bit 0 clear
mu.emu_start(CODE + syms["run"], RET, count=2000)
got = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF

print(f"run() = {got} (wasmtime oracle: {EXPECT})")
if got == EXPECT:
    print("ORACLE: PASS")
    sys.exit(0)
print("ORACLE: FAIL — call_indirect did not reach the callee (#594)")
sys.exit(1)
