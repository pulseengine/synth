#!/usr/bin/env python3
"""#649 — nonzero i64.const GLOBAL INITIALIZERS silently zeroed.

The decoder's `init_i32` captured only a leading `i32.const`; an i64 global's
init decoded to `None` and every consumer's `unwrap_or(0)` zeroed the slot.
#645 fixed the get/set PAIR lowering + width-aware slot layout — but a
`(global (mut i64) (i64.const X))` read BEFORE any set still returned 0.

This oracle runs the DEFAULT self-contained Cortex-M image (`--target
cortex-m4f`, the exact #649 verification shape) end to end, ARTIFACT-derived:

  1. unicorn executes the image's REAL startup (reset path) up to — not
     including — the `LDR r0,[pc]; BLX r0` call scaffold. With the fix the
     startup materializes the R9 globals table (both words of the i64 init +
     the i32 canary) and points R9 at it; on origin/main it sets only R10/R11.
  2. exports are then called with the startup's register state preserved
     (symbols from the ELF symtab, never disasm text) and compared against
     the SAME stateful sequence on ONE wasmtime instance:

       get_lo / get_hi          # init read BEFORE any set — the RED case
       get32                    # i32-declared-AFTER-i64 offset canary (init)
       set64(...); get_lo/get_hi  # the #645 set-then-get pin (no regression)
       set32(...); get32          # canary slot still independent after sets
       pure_add                 # global-free control

Red on origin/main (init reads diverge), green with the #649 fix.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/synthvenv/bin/python \
      scripts/repro/i64_global_init_649_differential.py
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
    UC_ARM_REG_R1,
    UC_ARM_REG_R9,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("i64_global_init_649.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
RET = 0x000F_0000  # inside the flash map, far past any code

I64_INIT = 0x123456789ABCDEF0
I32_INIT = 0x0C0FFEE1
SET64_VAL = 0xAABBCCDD11223344


def compile_synth(out):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "--all-exports",
           "-b", "arm", "--target", "cortex-m4f"]
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
    unicorn instance; the globals table (if any) is whatever the ARTIFACT's
    own reset path materialized — the harness fabricates nothing."""

    def __init__(self, code, base, syms):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(FLASH, 0x100000)
        self.mu.mem_map(RAM, RAM_SIZE)  # zeroed RAM: inits must come from startup
        self.mu.mem_write(base, code)
        # Initial SP from vector table word 0 (the image's own stack top).
        self.sp = int.from_bytes(code[0:4], "little")
        reset = syms.get("Reset_Handler")
        if reset is None:
            sys.exit("Reset_Handler missing from symtab")
        # Execute the real startup UP TO the `LDR r0,[pc,#4]; BLX r0` call
        # scaffold (we drive the calls ourselves). Locate it by its exact
        # 4-byte encoding within the startup region.
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
        for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
            self.mu.reg_write(reg, val & 0xFFFFFFFF)
        # SP/LR reset per call; R9/R10/R11 stay whatever STARTUP set them to.
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            self.mu.emu_start(faddr | 1, RET, count=100000)
        except UcError as e:
            return f"ERR:{e}"
        return self.mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


class WasmtimeRunner:
    """Stateful ground truth: ONE instance for the whole sequence."""

    def __init__(self):
        engine = wasmtime.Engine()
        module = wasmtime.Module.from_file(engine, str(WAT))
        self.store = wasmtime.Store(engine)
        self.inst = wasmtime.Instance(self.store, module, [])

    def call(self, fn, args=()):
        signed = [a - (1 << 32) if a >= (1 << 31) else a for a in args]
        r = self.inst.exports(self.store)[fn](self.store, *signed)
        return (r if r is not None else 0) & 0xFFFFFFFF


def sequence():
    lo, hi = SET64_VAL & 0xFFFFFFFF, SET64_VAL >> 32
    # The RED cases: init values read BEFORE any set.
    yield ("init-read get_lo (RED case)", "get_lo", ())
    yield ("init-read get_hi (RED case)", "get_hi", ())
    yield ("init-read i32-after-i64 canary", "get32", ())
    # The #645 pin: set-then-get across calls still correct.
    yield ("pin set64", "set64", (lo, hi))
    yield ("pin get_lo after set", "get_lo", ())
    yield ("pin get_hi after set", "get_hi", ())
    yield ("canary unclobbered by set64", "get32", ())
    yield ("pin set32", "set32", (0x5EED5EED,))
    yield ("pin get32 after set", "get32", ())
    yield ("control pure_add", "pure_add", (41, 1))


def main():
    out = "/tmp/i64ginit649.elf"
    compile_synth(out)
    code, base, syms = load(out)
    img = ImageRunner(code, base, syms)
    gt = WasmtimeRunner()
    print(f"=== #649 default image (cortex-m4f), startup R9 = "
          f"{img.startup_r9:#010x} ===")
    fails = 0
    for step, fn, fargs in sequence():
        exp = gt.call(fn, fargs)
        got = img.call(fn, fargs)
        is_get = fn not in ("set64", "set32")
        if not is_get:
            if isinstance(got, str):
                fails += 1
                print(f"  [BUG] {step}: {got}")
            continue
        match = got == exp
        if not match:
            fails += 1
        print(f"  [{'ok ' if match else 'BUG'}] {step}: {fn}{fargs} -> "
              f"{got if isinstance(got, str) else hex(got)}  (wasmtime {exp:#x})")
    print(f"\nORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
