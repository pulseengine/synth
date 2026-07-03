# #597: the Thumb-2 CallIndirect expansion put its `LSL #2` shift amount in
# the mov.w TYPE field (bits 5:4 → ASR #32) instead of imm2 (bits 7:6), so the
# table index was destroyed and EVERY call_indirect dispatched entry 0. A probe
# calling index 0 (#594's) cannot see it — this one drives indexes 0, 1 and 3
# of a 4-entry table with distinct results.
#
# Differential: emulate the Thumb object under unicorn (UC_MODE_THUMB) against
# the wasmtime oracle (run(0)=10, run(1)=11, run(3)=13).
#
# ArmOp::CallIndirect contract (same as the A32 path, #594): R11 holds the
# function-pointer table base; entry i is a 4-byte code address. Thumb entries
# carry bit 0 SET (BLX interworks on bit 0).
#
# Usage: python3 call_indirect_597_differential.py <elf>
#   <elf> = synth compile call_indirect_597.wat --target cortex-m3 \
#             --all-exports --relocatable --no-optimize -o <elf>
import struct
import sys

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/ci597.o"
CODE, TABLE, STK = 0x1000000, 0x3000000, 0x6000000
RET = CODE + 0xFFF0
# wasmtime --invoke run call_indirect_597.wat <idx>
EXPECT = {0: 10, 1: 11, 3: 13}

e = ELFFile(open(ELF, "rb"))
text = bytearray(e.get_section_by_name(".text").data())
# Symbols from the symtab, never from disasm text (host-dependent).
# Thumb STT_FUNC symbols carry bit 0 (interworking); mask it for the flat
# code offset (the emulation start address re-adds it via UC_MODE_THUMB).
st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
for need in ("run", "func_0", "func_1", "func_2"):
    if need not in syms:
        print(f"SYMBOL MISSING: {need}")
        sys.exit(1)

# Table layout mirrors the wat's (elem): [$f0, $f1, $f0, $f3] where the
# internal functions compile as func_0/func_1/func_2 in definition order.
table_entries = [syms["func_0"], syms["func_1"], syms["func_0"], syms["func_2"]]

fails = 0
for idx, want in sorted(EXPECT.items()):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(TABLE, 0x10000)
    mu.mem_map(STK, 0x100000)
    mu.mem_write(CODE, bytes(text))
    # table[i] = Thumb code address of entry i (bit 0 SET for BLX interwork)
    for i, off in enumerate(table_entries):
        mu.mem_write(TABLE + 4 * i, struct.pack("<I", (CODE + off) | 1))
    # Return pad: Thumb NOPs at RET (mapped inside the CODE region).
    mu.mem_write(RET, struct.pack("<HH", 0xBF00, 0xBF00))

    mu.reg_write(UC_ARM_REG_R0, idx)
    mu.reg_write(UC_ARM_REG_R11, TABLE)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)  # Thumb return address
    mu.emu_start((CODE + syms["run"]) | 1, RET, count=2000)
    got = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF

    ok = got == want
    fails += 0 if ok else 1
    print(f"run({idx}) = {got} (wasmtime oracle: {want}) {'OK' if ok else 'MISMATCH'}")

if fails == 0:
    print("ORACLE: PASS")
    sys.exit(0)
print(f"ORACLE: FAIL — {fails} index(es) misdispatched (#597)")
sys.exit(1)
