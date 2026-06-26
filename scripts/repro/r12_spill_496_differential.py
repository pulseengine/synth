#!/usr/bin/env python3
"""#496 (epic #242) — EXECUTION-validate the DEFAULT optimized-path register-
exhaustion fix.

The optimized ARM path (`optimizer_bridge.rs::ir_to_arm`, the default
non-`--relocatable` self-contained image) used **R12/IP** as a last-resort
scratch when its R4-R8 pool was exhausted. R12 is the encoder's indexed-load
base scratch (#212), so under real register pressure the "dest written before
R12 used" assumption broke: two folds collide on R12, or an R12 value survives
across a later MemLoad's `add ip,ip,#off` base math — a silent miscompile.
**Both silicon fixtures were victims on the default path**: `control_step`
(0x00210A55) execution-faulted (`lsl ip,r4,ip` clobbered → `add ip,ip,ip` =
2×base → ldrh READ_UNMAPPED), `flight_seam_flat` produced wrong values.

The fix flags pool exhaustion and DECLINES the whole function to the direct
selector (which spills correctly), instead of borrowing R12. This harness proves
the property that matters: the **default** `synth compile` (no `--relocatable`,
i.e. the path a self-contained image actually takes) now executes
bit-for-bit like wasmtime on both fixtures.

wasmtime is ground truth; unicorn runs synth's Thumb-2 output compiled WITHOUT
`--relocatable`. Symbols come from the ELF symtab (SHT_SYMTAB), not `synth
disasm` text — the disasm renders host-dependently (the ARM decoder misreads
Thumb bytes on a bare runner). The linear-memory base is read from the
`__linear_memory_base` symbol and both R11 and the unicorn mapping use it, so
absolute and R11-relative addressing both resolve.

NON-VACUITY: pre-fix, `control_step` faulted and `flight_seam_flat` mismatched on
this exact (default-path) harness; the fix changed both functions' bytes
(control_step 626→464, flat 2096→1070). A regression that reinstates the R12
borrow re-breaks execution here.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/r12_spill_496_differential.py
Exits nonzero on any mismatch or fault.
"""
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

REPRO = Path(__file__).parent
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

CODE, STK, RET = 0x100000, 0x900000, 0x300000
LIN_SIZE = 0x20000  # cover control_step's 2-page .linear_memory

ARG_REGS = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)


def compile_default(wasm, elf):
    """Compile via the DEFAULT optimized path — NO --relocatable. This is the
    self-contained-image path #496 fixes (and the one that miscompiled)."""
    r = subprocess.run(
        [SYNTH, "compile", str(wasm), "-o", elf, "--target", "cortex-m4",
         "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    if r.returncode != 0:
        sys.exit(f"compile failed for {wasm}: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return code, base, syms


def run_unicorn(code, base, faddr, lin_base, lin_writes, args):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(lin_base, LIN_SIZE)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    for off, data in lin_writes:
        mu.mem_write(lin_base + off, data)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, lin_base)
    for r in ARG_REGS:
        mu.reg_write(r, 0)
    for r, v in zip(ARG_REGS, args):
        mu.reg_write(r, v & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + faddr - base) | 1, RET, count=200000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


# ---- control_step: 4 args, .rodata table at linmem offset 0x10000 ----
CS_VECTORS = [
    (3000, 50, 40, 0),   # gale's reference -> 0x00210A55
    (0, 0, 0, 0), (1500, 0, 0, 0), (3000, 50, 40, 1), (2000, 100, 200, 5),
    (500, 5, 80, 1000), (65535, 127, 127, 3), (1, 1, 1, 1), (2645, 10, 20, 0),
    (4000, 200, 30, 7), (123, 45, 67, 89), (3000, 50, 40, 255), (0xFFFFFFFF, 0, 0, 0),
]
CS_RODATA_OFF, CS_RODATA_END = 0x10000, 0x20000


def test_control_step():
    wasm = REPRO / "control_step.wasm"
    elf = "/tmp/cs496.elf"
    compile_default(wasm, elf)
    code, base, syms = load(elf)
    lin_base = syms["__linear_memory_base"]
    fa = syms.get("control_step_decide") or syms["func_0"]

    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wasm.read_bytes())

    fails = 0
    for vec in CS_VECTORS:
        st = wasmtime.Store(eng)
        inst = wasmtime.Instance(st, mod, [])
        signed = [v - (1 << 32) if v >= 1 << 31 else v for v in vec]
        exp = inst.exports(st)["control_step_decide"](st, *signed) & 0xFFFFFFFF
        rodata = bytes(inst.exports(st)["memory"].read(st, CS_RODATA_OFF, CS_RODATA_END))
        got = run_unicorn(code, base, fa, lin_base,
                          [(CS_RODATA_OFF, rodata)], vec)
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        shown = f"0x{got:08X}" if isinstance(got, int) else got
        print(f"{'OK  ' if ok else 'FAIL'} control_step_decide{vec} = {shown} "
              f"(wasmtime 0x{exp:08X})")
    return fails


# ---- flight_seam_flat: flat flight_algo(ST_OFF, S_OFF), 1-page memory ----
FS_ST_OFF, FS_S_OFF = 0x1000, 0x2000


def fs_st_init():
    b = bytearray(64)
    struct.pack_into("<i", b, 0, 1000)
    struct.pack_into("<i", b, 4, -500)
    struct.pack_into("<i", b, 8, 200)
    struct.pack_into("<i", b, 24, 7)
    return bytes(b)


def fs_s_init():
    b = bytearray(32)
    for i, v in enumerate([100, -50, 30, 300, -200]):
        struct.pack_into("<h", b, i * 2, v)
    return bytes(b)


def test_flight_seam_flat():
    wasm = REPRO / "flight_seam_flat.wasm"
    elf = "/tmp/fsflat496.elf"
    compile_default(wasm, elf)
    code, base, syms = load(elf)
    lin_base = syms["__linear_memory_base"]
    fa = syms.get("flight_algo") or syms["func_0"]

    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wasm.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    mem = inst.exports(st)["memory"]
    mem.write(st, fs_st_init(), FS_ST_OFF)
    mem.write(st, fs_s_init(), FS_S_OFF)
    exp = inst.exports(st)["flight_algo"](st, FS_ST_OFF, FS_S_OFF) & 0xFFFFFFFF

    got = run_unicorn(code, base, fa, lin_base,
                      [(FS_ST_OFF, fs_st_init()), (FS_S_OFF, fs_s_init())],
                      (FS_ST_OFF, FS_S_OFF))
    ok = isinstance(got, int) and got == exp
    shown = f"0x{got:08X}" if isinstance(got, int) else got
    print(f"{'OK  ' if ok else 'FAIL'} flight_algo(0x{FS_ST_OFF:x},0x{FS_S_OFF:x}) "
          f"= {shown} (wasmtime 0x{exp:08X})")
    return 0 if ok else 1


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    fails = test_control_step() + test_flight_seam_flat()
    print("\nORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
