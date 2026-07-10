#!/usr/bin/env python3
"""#687 — `--stack-layout=low`: stack at the SRAM bottom, overflow BusFaults.

Today's self-contained Cortex-M image puts the initial SP at the TOP of SRAM,
growing DOWN toward the R9 globals table and linear memory — a stack overflow
silently corrupts them long before anything faults. `--stack-layout=low`
reserves `--stack-size` bytes at the SRAM BOTTOM (SP init = SRAM start +
stack size) and shifts linmem/globals (and the optimized path's absolute
`0x2000_0100` base) UP by the stack size, so overflow descends past
`0x2000_0000` into unmapped/reserved space and faults on the FIRST errant
push — every Cortex-M, no MPU.

This oracle runs the REAL self-contained image (vector-table SP + startup)
under unicorn, both layouts, artifact-derived:

  RED  (high, today's hazard): plant 8 magic canary words in linmem, then
       recurse until overflow. The run faults only at the SRAM floor — AFTER
       the stack swept the canaries: canaries CORRUPTED, silently.
  GREEN (low): same recursion faults at the SRAM start after descending only
       the reserved stack — UC_ERR_WRITE_UNMAPPED with SP at the floor and
       ALL canaries INTACT (the fault precedes any linmem damage).
  TRANSPARENT: in-budget calls (set/get canary via the optimized path's
       absolute base, recursion within budget, arithmetic) match wasmtime
       under BOTH layouts — the layout shift is invisible when the stack
       doesn't overflow.
  SHIFT PIN: the canaries' absolute SRAM addresses under low sit exactly
       `stack_size` above their high-layout addresses (the uniform shift).

Run (deps: wasmtime unicorn pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/stack_layout_687_differential.py
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
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("stack_canary_687.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
RET = 0x000F_0000  # inside the flash map, far past any code
MAGIC = 0xC0DECAFE
STACK_SIZE = 4096  # the --stack-layout=low default
DEEP = 500_000  # recursion depth that overflows either layout's stack


def compile_synth(out, low):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "--all-exports",
           "-b", "arm", "--target", "cortex-m4"]
    if low:
        cmd += ["--stack-layout", "low"]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed ({'low' if low else 'high'}): {r.stderr}")


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
    """The self-contained image, startup included (the #649 pattern): one
    persistent unicorn instance; SP comes from the image's OWN vector table,
    R9/R10/R11 from its OWN reset path — the harness fabricates nothing."""

    def __init__(self, code, base, syms):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(FLASH, 0x100000)
        self.mu.mem_map(RAM, RAM_SIZE)  # NOTHING below RAM is mapped (#687)
        # GI-FPU-002 (#619): FPU-target startup writes SCB->CPACR (0xE000ED88)
        # to enable CP10/CP11 — map the System Control Space page so the
        # reset-path replay does not fault on it (real silicon has this reg).
        self.mu.mem_map(0xE000E000, 0x1000)
        self.mu.mem_write(base, code)
        # Initial SP from vector table word 0 (layout-dependent under #687).
        self.sp = int.from_bytes(code[0:4], "little")
        reset = syms.get("Reset_Handler")
        if reset is None:
            sys.exit("Reset_Handler missing from symtab")
        # Execute the real startup UP TO the `LDR r0,[pc,#4]; BLX r0` call
        # scaffold (we drive the calls ourselves).
        stop = code.find(b"\x01\x48\x80\x47", (reset & ~1) - base)
        if stop < 0:
            sys.exit("startup call scaffold (LDR r0/BLX r0) not found")
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.emu_start(reset | 1, base + stop, count=10000)

    def call(self, fn, args=(), count=200000):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
        for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
            self.mu.reg_write(reg, val & 0xFFFFFFFF)
        # SP/LR reset per call; R9/R10/R11 stay whatever STARTUP set them to.
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            self.mu.emu_start(faddr | 1, RET, count=count)
        except UcError as e:
            return f"ERR:{e}"
        return self.mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF

    def canary_addrs(self):
        ram = self.mu.mem_read(RAM, RAM_SIZE)
        pat = MAGIC.to_bytes(4, "little")
        return [RAM + i for i in range(0, RAM_SIZE - 3, 4)
                if ram[i:i + 4] == pat]


class WasmtimeRunner:
    def __init__(self):
        engine = wasmtime.Engine()
        module = wasmtime.Module.from_file(engine, str(WAT))
        self.store = wasmtime.Store(engine)
        self.inst = wasmtime.Instance(self.store, module, [])

    def call(self, fn, args=()):
        signed = [a - (1 << 32) if a >= (1 << 31) else a for a in args]
        r = self.inst.exports(self.store)[fn](self.store, *signed)
        return (r if r is not None else 0) & 0xFFFFFFFF


def in_budget_sequence():
    yield ("control add", "add", (41, 1))
    yield ("in-budget recursion (20 deep)", "recurse", (20,))
    yield ("plant canaries (optimized-path abs base)", "set_canary", ())
    for i in range(8):
        yield (f"read canary word {i} back", "get_canary", (i,))


def run_layout(low):
    name = "low" if low else "high"
    out = f"/tmp/stack687_{name}.elf"
    compile_synth(out, low)
    img = ImageRunner(*load(out))
    gt = WasmtimeRunner()
    fails = 0

    print(f"=== --stack-layout={name}: image SP init {img.sp:#010x} ===")

    # 1) TRANSPARENT: in-budget behaviour matches wasmtime under both layouts.
    for step, fn, fargs in in_budget_sequence():
        exp = gt.call(fn, fargs)
        got = img.call(fn, fargs)
        if fn == "set_canary":
            if isinstance(got, str):
                fails += 1
                print(f"  [BUG] {step}: {got}")
            continue
        ok = got == exp
        fails += 0 if ok else 1
        print(f"  [{'ok ' if ok else 'BUG'}] {step}: {fn}{fargs} -> "
              f"{got if isinstance(got, str) else hex(got)}  (wasmtime {exp:#x})")

    # 2) Locate the planted canaries in SRAM (artifact-derived, no layout math).
    addrs = img.canary_addrs()
    if len(addrs) != 8:
        fails += 1
        print(f"  [BUG] expected 8 canary words in SRAM, found {len(addrs)}")
    else:
        print(f"  [ok ] 8 canaries at {addrs[0]:#010x}..{addrs[-1]:#010x}")

    # 3) OVERFLOW: recurse far past any budget. Both layouts eventually fault
    #    (nothing below SRAM is mapped) — what differs is WHAT DIED FIRST.
    res = img.call("recurse", (DEEP,), count=20_000_000)
    sp = img.mu.reg_read(UC_ARM_REG_SP)
    if not (isinstance(res, str) and res.startswith("ERR:")):
        fails += 1
        print(f"  [BUG] deep recursion did not fault (got {res})")
        return fails, addrs, None
    print(f"  [ok ] deep recursion faulted: {res} (SP {sp:#010x})")
    intact = sum(1 for a in addrs
                 if img.mu.mem_read(a, 4) == MAGIC.to_bytes(4, "little"))

    if low:
        # GREEN: the fault came at the SRAM floor after only the reserved
        # stack — BEFORE any linmem byte changed.
        if intact == len(addrs):
            print(f"  [ok ] GREEN: BusFault below SRAM before ANY canary "
                  f"changed ({intact}/8 intact)")
        else:
            fails += 1
            print(f"  [BUG] low layout corrupted linmem: {intact}/8 intact")
        if sp > RAM + STACK_SIZE:
            fails += 1
            print(f"  [BUG] fault SP {sp:#010x} above the reserved stack")
    else:
        # RED: today's hazard — the stack swept linmem long before faulting.
        if intact < len(addrs):
            print(f"  [ok ] RED evidence: stack overflow SILENTLY corrupted "
                  f"linmem canaries ({8 - intact}/8 clobbered) before any fault")
        else:
            fails += 1
            print("  [BUG] expected the high-layout overflow to corrupt the "
                  "canaries (red case is vacuous)")
    return fails, addrs, intact


def main():
    fails_high, addrs_high, _ = run_layout(low=False)
    fails_low, addrs_low, _ = run_layout(low=True)
    fails = fails_high + fails_low

    # 4) SHIFT PIN: the low layout is the high layout shifted UP by the
    #    reserved stack size — canary for canary.
    if len(addrs_high) == 8 and len(addrs_low) == 8:
        if [a + STACK_SIZE for a in addrs_high] == addrs_low:
            print(f"\n[ok ] uniform shift: low canaries sit exactly "
                  f"{STACK_SIZE:#x} above their high-layout addresses")
        else:
            fails += 1
            print(f"\n[BUG] shift mismatch: high {addrs_high[0]:#010x}.. vs "
                  f"low {addrs_low[0]:#010x}..")

    print(f"\nORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
