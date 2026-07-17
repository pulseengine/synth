#!/usr/bin/env python3
"""#761 — self-contained --cortex-m full-page linmem view OVERLAPS the R9 globals
table at the top of SRAM (a silent global<->linmem ALIAS: the worst class).

Geometry (pre-fix): the startup materializes the R9 globals table at
`linmem_base + memory_size` where `linmem_base` is the startup R11 base
(0x2000_0000). But the COMPILED FUNCTIONS address linear memory at
`optimized_linmem_base` = 0x2000_0100 (0x100 above R11, the #687 contract). The
globals placement forgot that 0x100 shift, so for a `(memory 1)` module the R9
table sits at 0x2001_0000 while a function's store to wasm offset 0xFF00 lands at
0x2000_0100 + 0xFF00 = 0x2001_0000 — EXACTLY global slot 0. The top 0x100 of the
first page ALIASES the globals table.

This oracle boots the DEFAULT self-contained Cortex-M image (`--target
cortex-m4`) end to end through its REAL reset path (which materializes R9), then
calls `overlap_probe` and compares against wasmtime:

  overlap_probe: store 0xDEADBEEF to mem[0xFF00]; return global 0 (init 0xABCD).
    wasmtime (correct): 0xABCD   — the linmem cell and the global are disjoint.
    pre-fix synth:      0xDEADBEEF — the store landed on global 0's storage.

  disjoint_probe (regression witness): store 0xDEADBEEF to mem[0x0000]; return
    global 0. Both = 0xABCD before AND after — offset 0 never hits globals, so
    the fix must not perturb it.

RED on origin/main (overlap_probe diverges), GREEN with the #761 fix.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 \
      scripts/repro/mem761_linmem_r9_overlap_differential.py
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R9,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("mem761_linmem_r9_overlap.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
RET = 0x000F_0000  # inside the flash map, far past any code


def compile_synth(out):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "--all-exports",
           "-b", "arm", "--target", "cortex-m4"]
    # #687: EXTRA_SYNTH_FLAGS (e.g. "--stack-layout low") re-runs this oracle
    # against a shifted self-contained layout. Default empty = unchanged.
    cmd += os.environ.get("EXTRA_SYNTH_FLAGS", "").split()
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


class ImageRunner:
    """The DEFAULT self-contained image, startup included: one persistent
    unicorn instance; R9 is whatever the ARTIFACT's own reset path set it to."""

    def __init__(self, code, base, syms):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(FLASH, 0x100000)
        self.mu.mem_map(RAM, RAM_SIZE)  # zeroed RAM: inits must come from startup
        self.mu.mem_map(0xE000E000, 0x1000)  # System Control Space (CPACR etc.)
        self.mu.mem_write(base, code)
        self.sp = int.from_bytes(code[0:4], "little")
        reset = syms.get("Reset_Handler")
        if reset is None:
            sys.exit("Reset_Handler missing from symtab")
        stop = code.find(b"\x01\x48\x80\x47", (reset & ~1) - base)
        if stop < 0:
            sys.exit("startup call scaffold (LDR r0/BLX r0) not found")
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.emu_start(reset | 1, base + stop, count=10000)
        self.startup_r9 = self.mu.reg_read(UC_ARM_REG_R9)

    def call(self, fn, args=()):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
        for reg, val in zip((UC_ARM_REG_R0,), args):
            self.mu.reg_write(reg, val & 0xFFFFFFFF)
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            self.mu.emu_start(faddr | 1, RET, count=100000)
        except UcError as e:
            return f"ERR:{e}"
        return self.mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


class WasmtimeRunner:
    def __init__(self):
        engine = wasmtime.Engine()
        module = wasmtime.Module.from_file(engine, str(WAT))
        self.store = wasmtime.Store(engine)
        self.inst = wasmtime.Instance(self.store, module, [])

    def call(self, fn, args=()):
        r = self.inst.exports(self.store)[fn](self.store, *args)
        return (r if r is not None else 0) & 0xFFFFFFFF


def main():
    out = "/tmp/mem761.elf"
    compile_synth(out)
    code, base, syms = load(out)
    img = ImageRunner(code, base, syms)
    gt = WasmtimeRunner()
    print(f"=== #761 default image (cortex-m4), startup R9 = "
          f"{img.startup_r9:#010x} ===")
    fails = 0
    for step, fn in [
        ("OVERLAP: store mem[0xFF00], read global 0 (RED case)", "overlap_probe"),
        ("DISJOINT: store mem[0x0000], read global 0 (regression witness)",
         "disjoint_probe"),
        ("MEM: store then load mem[0xFF00] (store-lands-in-linmem witness)",
         "mem_ff00_probe"),
    ]:
        exp = gt.call(fn)
        got = img.call(fn)
        match = got == exp
        if not match:
            fails += 1
        print(f"  [{'ok ' if match else 'BUG'}] {step}: {fn} -> "
              f"{got if isinstance(got, str) else hex(got)}  (wasmtime {exp:#x})")
    print(f"\nORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
