#!/usr/bin/env python3
"""#758 — the DEFAULT self-contained `--cortex-m` image silently DROPS active
`(data …)` segments.

Root cause: `build_multi_func_cortex_m_elf` reserved `.linear_memory` as NoBits
(BSS) and the generated `Reset_Handler` had no data-copy loop, so the segment
bytes never reached RAM — every load from an initialized region read 0. The
self-contained image has no loader that populates RAM from PT_LOAD, so the fix
ships the segments in a flash ROM image (appended to `.text`) and copies
ROM→RAM at reset (the classic crt0 `.data` init).

This oracle runs the DEFAULT self-contained image (`--cortex-m`, no
--relocatable, no native-pointer ABI) END TO END, ARTIFACT-derived — modelled
on the #649 startup oracle:

  1. unicorn maps a ZEROED FLASH + ZEROED RAM (no PT_LOAD population — inits
     must come from the reset path), writes ONLY `.text` (which carries the ROM
     image after the fix), and executes the REAL `Reset_Handler` up to — not
     including — the `LDR r0,[pc,#4]; BLX r0` call scaffold. With the fix the
     reset path copies the segment bytes ROM→RAM; on origin/main it does not.
  2. each export is then called with the startup's register state preserved
     (symbols from the ELF symtab, never disasm text) and compared to wasmtime.

Covered: three segments (a word load, a high-word load, an unaligned segment, a
byte load mid-segment), an OVERLAPPING pair pinning in-order "later segment
wins" semantics, and a load from a region NO segment initializes (must read 0 —
the fix must not over-copy or corrupt BSS).

Red on origin/main (initialized loads read 0), green with the fix.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/w758venv/bin/python \
      scripts/repro/self_contained_data_758_differential.py
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
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("self_contained_data_758.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
RET = 0x000F_0000  # inside the flash map, far past any code


def compile_synth(out):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "--all-exports",
           "-b", "arm", "--target", "cortex-m3"]
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
    unicorn instance on ZEROED RAM. Whatever ends up in linear memory is only
    what the ARTIFACT's own reset path copied there — the harness fabricates
    nothing."""

    def __init__(self, code, base, syms):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(FLASH, 0x100000)
        self.mu.mem_map(RAM, RAM_SIZE)  # zeroed RAM: inits must come from startup
        self.mu.mem_map(0xE000E000, 0x1000)  # SCS page (FPU-target startup)
        self.mu.mem_write(base, code)
        self.sp = int.from_bytes(code[0:4], "little")
        reset = syms.get("Reset_Handler")
        if reset is None:
            sys.exit("Reset_Handler missing from symtab")
        # Execute the real startup UP TO the `LDR r0,[pc,#4]; BLX r0` scaffold.
        stop = code.find(b"\x01\x48\x80\x47", (reset & ~1) - base)
        if stop < 0:
            sys.exit("startup call scaffold (LDR r0/BLX r0) not found")
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.emu_start(reset | 1, base + stop, count=100000)

    def call(self, fn):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
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

    def call(self, fn):
        r = self.inst.exports(self.store)[fn](self.store)
        return (r if r is not None else 0) & 0xFFFFFFFF


def main():
    out = "/tmp/selfdata758.elf"
    compile_synth(out)
    code, base, syms = load(out)
    img = ImageRunner(code, base, syms)
    gt = WasmtimeRunner()
    print("=== #758 default self-contained image (cortex-m3), "
          "ROM->RAM data copy at reset ===")
    fails = 0
    for fn in ("lo", "hi", "segB", "byteC", "ovl", "zero"):
        exp = gt.call(fn)
        got = img.call(fn)
        match = isinstance(got, int) and got == exp
        if not match:
            fails += 1
        shown = hex(got) if isinstance(got, int) else got
        print(f"  [{'ok ' if match else 'BUG'}] {fn}() -> {shown}  "
              f"(wasmtime {exp:#x})")
    print(f"\nORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
