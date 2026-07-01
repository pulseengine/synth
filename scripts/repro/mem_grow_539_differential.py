#!/usr/bin/env python3
"""#539 — EXECUTION-validate the memory.grow(0) fix on both ARM lowering paths.

Before the fix, every `memory.grow` lowered to a constant `-1`, so the legal
`memory.grow(0)` "return current size" idiom (WASM Core §4.4.7 — growing by zero
pages can never fail) wrongly reported failure. The fix folds `i32.const 0;
memory.grow` → `memory.size` up front (semantically identical), which also fixed
a latent optimized-path bug where `memory.size` returned BYTES (`MOV R10`) rather
than PAGES (`LSR R10,#16`).

This harness compiles `mem_grow_539.wat` on BOTH ARM paths (optimized = default,
direct = `--relocatable`), runs each export under unicorn (Thumb, R10 = memory
size in bytes as the runtime startup sets it), and checks:
  - `sz`    == 3   (current pages; catches the MOV-vs-LSR memory.size bug)
  - `grow0` == 3   (grow-by-0 returns current size — the #539 fix)
  - `grow2` == -1  (grow-by->0 on FIXED memory returns -1; this is the sound,
                    documented behavior and legitimately differs from wasmtime,
                    whose memory can actually grow — so grow>0 is asserted
                    directly, not against wasmtime)

`sz`/`grow0` are also cross-checked against wasmtime (a FRESH instance per call —
`memory.grow` mutates the store, so a shared instance would pollution the oracle).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/mem_grow_539_differential.py
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
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("mem_grow_539.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x900000, 0x300000
PAGES = 3
R10 = PAGES * 65536  # runtime memory size in bytes (as startup sets R10)


def wasmtime_run(fn):
    # FRESH instance per call: memory.grow mutates the store, so a shared
    # instance would let grow2 inflate a later memory.size read.
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    return wasmtime.Instance(store, module, []).exports(store)[fn](store)


def compile_arm(out, relocatable):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"compile failed/skipped (reloc={relocatable}): {r.stderr}")


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


def unicorn_run(code, base, faddr):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R10, R10)
    mu.reg_write(UC_ARM_REG_R11, 0x20000000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    raw = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    return struct.unpack("<i", struct.pack("<I", raw))[0]


def main():
    # (export, expected). grow2 is asserted to -1 directly (fixed memory cannot
    # grow; that is the sound behavior and differs from wasmtime by design).
    cases = [
        ("sz", wasmtime_run("sz")),        # 3
        ("grow0", wasmtime_run("grow0")),  # 3 — the #539 fix
        ("grow2", -1),                     # fixed-memory: grow>0 -> -1
    ]
    fails = 0
    for relocatable, label in ((False, "optimized"), (True, "direct   ")):
        out = f"/tmp/mg539_{'rel' if relocatable else 'opt'}.o"
        compile_arm(out, relocatable)
        code, base, syms = load(out)
        for fn, expect in cases:
            got = unicorn_run(code, base, syms[fn])
            ok = got == expect
            if not ok:
                fails += 1
            note = "" if fn != "grow2" else "  (fixed-mem: -1 is sound; wasmtime grows)"
            print(f"{'OK ' if ok else 'BUG'} [{label}] {fn:6} synth={got} "
                  f"expect={expect}{note}")
    print("\nRESULT:", "PASS — memory.grow(0) returns current size on both paths"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
