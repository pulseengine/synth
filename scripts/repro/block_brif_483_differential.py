#!/usr/bin/env python3
"""#483 (epic #242) — EXECUTION-validate optimized-path block/br_if lowering.

On the OPTIMIZED (non-`--relocatable`) ARM path, a forward `block` + `br_if`
lowered to a conditional branch whose target landed MID-INSTRUCTION: the branch
targeted the id pushed for the `Block` opener, but the only emitted label sat at
the matching `End` carrying the End's *own* id — so the target resolved against
an id no label held and was left as the unpatched offset-0 placeholder. A
companion size-estimator gap (i32.store16 → `Strh`, a 4-byte `.w` encoding, was
sized as 2) drifted `byte_offsets` so even a resolved branch missed by 2 bytes.

This harness compiles the fixture via the optimized path, runs each function
under unicorn (UC_ARCH_ARM / Thumb) with the linear memory mapped at the absolute
base the optimized path materializes, and asserts the resulting MEMORY is
bit-identical to wasmtime ground truth across both branch directions (taken /
not-taken). The functions write memory and return nothing, so memory is the
observable. Before the fix, `init_branch(0)` (br_if taken → block skipped) wrote
the guarded fields anyway.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/block_brif_483_differential.py
Exits nonzero on any mismatch.
"""
import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_SP

WAT = Path(__file__).with_name("block_brif_483.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
# Absolute linear-memory base the optimized (non-relocatable) path materializes
# for a const address: `movw ip,#0x100; movt ip,#0x2000` → 0x20000100 (see #197).
LINMEM = 0x20000100
MEM_WINDOW = 64      # bytes of memory compared against ground truth
# (function, [sel values exercising both branch directions])
CASES = {"init_branch": [0, 1], "nested": [0, 1]}


def compile_optimized(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def wasm_mem(func, sel):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    inst.exports(st)[func](st, sel)
    return bytes(inst.exports(st)["memory"].read(st, 0, MEM_WINDOW))


def run_rv(code, base, addr, sel):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(LINMEM & ~0xFFFF, 0x20000)  # page-aligned region covering LINMEM
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_R0, sel & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.emu_start(addr | 1, ret, timeout=5_000_000)
    return bytes(mu.mem_read(LINMEM, MEM_WINDOW))


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    elf = "/tmp/block_brif_483.elf"
    compile_optimized(elf)
    code, base, syms = load(elf)

    fails = 0
    for func, sels in CASES.items():
        for sel in sels:
            gt = wasm_mem(func, sel)
            got = run_rv(code, base, syms[func], sel)
            ok = got == gt
            if not ok:
                fails += 1
            print(f"{'OK  ' if ok else 'FAIL'} {func}(sel={sel})")
            if not ok:
                diff = [(i, gt[i], got[i]) for i in range(MEM_WINDOW) if gt[i] != got[i]]
                print(f"     mem diffs (off, wasmtime, synth): {diff}")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
