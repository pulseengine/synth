#!/usr/bin/env python3
"""#275 — the DIRECT reachable call graph must EXECUTE on the self-contained
`--cortex-m` image (no --relocatable, no loader).

Only `entry` is exported. It calls two NON-exported helpers (`mid`, `add5`),
and `mid` calls a third (`leaf`) — so the correct result depends on the whole
transitive closure of static `call`s being COMPILED INTO the image and every
internal BL patched to the emitted callee's address. `dead` is unreachable and
must be irrelevant.

This is an EXECUTION differential (not an `nm`/symtab presence check): a helper
that is present but mis-patched, or a helper that is dropped, both change the
numeric result. Ground truth is wasmtime; the ARM image runs on unicorn with
its OWN Reset_Handler startup (the harness fabricates nothing in RAM).

Non-vacuity — this gate PROVABLY catches the pre-#235 exports-only drop: set
EXPORTS_ONLY_275=1 to compile with a synth built with the reachability filter
bypassed (helpers absent). Then `entry`'s BL targets are missing and the image
diverges (RED). With the shipped reachability walk (#235) every helper is
present and BL-resolved, so it matches for every vector (GREEN).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/w29venv/bin/python \
      scripts/repro/reachable_callgraph_275_selfcontained_differential.py
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

WAT = Path(__file__).with_name("reachable_callgraph_275_selfcontained.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
RET = 0x000F_0000  # inside the flash map, far past any code


def compile_synth(out):
    env = {"PATH": "/usr/bin:/bin"}
    # Thread the non-vacuity hatch through the hermetic env (see module docstring).
    if os.environ.get("EXPORTS_ONLY_275"):
        env["EXPORTS_ONLY_275"] = os.environ["EXPORTS_ONLY_275"]
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "--all-exports",
           "-b", "arm", "--target", "cortex-m3"]
    cmd += os.environ.get("EXTRA_SYNTH_FLAGS", "").split()
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    etype = f["e_type"]  # ET_EXEC = self-contained; ET_REL = needs a linker
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    return code, base, syms, etype


class ImageRunner:
    """The DEFAULT self-contained image, startup included: one persistent
    unicorn instance on ZEROED RAM. Only what the ARTIFACT's own reset path
    copies to RAM is there — the harness fabricates nothing."""

    def __init__(self, code, base, syms):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(FLASH, 0x100000)
        self.mu.mem_map(RAM, RAM_SIZE)
        self.mu.mem_map(0xE000E000, 0x1000)  # SCS page
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

    def call(self, fn, arg):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, RET | 1)
        self.mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
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

    def call(self, fn, arg):
        r = self.inst.exports(self.store)[fn](self.store, arg)
        return (r if r is not None else 0) & 0xFFFFFFFF


VECTORS = [0, 1, 2, 5, 17, 100, 0x1000]


def main():
    out = "/tmp/reachable275.elf"
    compile_synth(out)
    code, base, syms, etype = load(out)
    mode = "EXPORTS-ONLY (reachability bypassed)" if os.environ.get(
        "EXPORTS_ONLY_275") else "shipped reachability walk (#235)"
    print(f"=== #275 self-contained reachable-callgraph EXECUTION [{mode}] ===")
    # A self-contained --cortex-m image MUST be an executable (ET_EXEC). If a
    # reachable helper was dropped, `entry`'s BL to it becomes an EXTERNAL
    # relocation, and the builder degrades to a link-me ET_REL object with no
    # Reset_Handler — not runnable standalone. That is the pre-#235 #275 drop.
    if etype != "ET_EXEC":
        print(f"  [BUG] output is {etype}, not ET_EXEC — a reachable helper was "
              "dropped, so the image is NOT self-contained (needs a linker).")
        print("\nORACLE: FAIL (1 divergence — image is not self-contained)")
        sys.exit(1)
    img = ImageRunner(code, base, syms)
    gt = WasmtimeRunner()
    # Presence probe (informational — internal callees are emitted as func_N):
    #   func_0=leaf, func_1=mid, func_2=add5 are the reachable closure; func_3
    #   (dead) is unreachable and must be ABSENT (a closure, not "emit all").
    for h in ("func_0", "func_1", "func_2"):
        print(f"  symtab: {h} {'present' if h in syms else 'ABSENT'}")
    print(f"  symtab: func_3 (dead) "
          f"{'PRESENT (unexpected)' if 'func_3' in syms else 'absent (ok)'}")
    fails = 0
    for x in VECTORS:
        exp = gt.call("entry", x)
        got = img.call("entry", x)
        match = isinstance(got, int) and got == exp
        if not match:
            fails += 1
        shown = hex(got) if isinstance(got, int) else got
        print(f"  [{'ok ' if match else 'BUG'}] entry({x}) -> {shown}  "
              f"(wasmtime {exp:#x})")
    print(f"\nORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
