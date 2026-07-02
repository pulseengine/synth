#!/usr/bin/env python3
"""#543 Phase 2 / VCR-DMA-001 — EXECUTION-validate the volatile DMA-window back-off.

`--volatile-segment <base>:<len>` must change ACCESS PATTERNS, never RESULTS:
with the ranges marked, base-CSE (#468, SYNTH_BASE_CSE=1) keeps every in-window
access as verbatim per-access materialize-and-access codegen (and const-CSE
declines wholesale), but the memory the function computes must stay bit-identical
to wasmtime ground truth in EVERY mode. This harness runs the fixture's
`dma_window(v)` under unicorn in four builds —

  base    : default env, no ranges           (the pre-#543 baseline)
  folded  : SYNTH_BASE_CSE=1, no ranges      (all 4 const-address stores fold)
  window  : SYNTH_BASE_CSE=1, --volatile-segment 0x100:16
            (the 2 window stores stay verbatim, the 2 outside still fold)
  cover   : SYNTH_BASE_CSE=1, --volatile-segment 0x80:144
            (covers all 4 → base-CSE fully declines)

— and asserts the resulting LINEAR MEMORY (fields 0x80/0x84 outside, 0x100/0x104
inside the DMA window) matches wasmtime for several input values.

NON-VACUITY (the byte-shape claims, mirrored from
crates/synth-cli/tests/volatile_segment_phase2_543.rs): folded < window < base
.text sizes, and cover ≡ base byte-identical (every store survives verbatim).

Run (needs wasmtime + unicorn + pyelftools; synth binary via $SYNTH or the
default release path):
  python scripts/repro/volatile_segment_543_differential.py
Exits nonzero on any mismatch or vacuity failure.
"""

import os
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_SP

SYNTH = os.environ.get("SYNTH", "./target/release/synth")
WAT = "scripts/repro/volatile_segment_543.wat"
FUNC = "dma_window"
# The optimized path materializes this absolute linear-memory base.
LINMEM = 0x20000100
CODE, STK, RET = 0x200000, 0x90000, 0x300000
# Fields written by the fixture: 0x80/0x84 outside, 0x100/0x104 inside the window.
FIELDS = [0x80, 0x84, 0x100, 0x104]

BUILDS = {
    "base": (False, []),
    "folded": (True, []),
    "window": (True, ["--volatile-segment", "0x100:16"]),
    "cover": (True, ["--volatile-segment", "0x80:144"]),
}


def compile_elf(out, base_cse, extra):
    env = {"PATH": "/usr/bin:/bin"}
    if base_cse:
        env["SYNTH_BASE_CSE"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", WAT, "-o", out, "-b", "arm", "--target", "cortex-m4",
         "--all-exports", *extra],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (base_cse={base_cse}, extra={extra}): {r.stderr}")


def load(elf):
    """Return (code_bytes, sh_addr, func_entry_offset)."""
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    fa = None
    # Resolve via the symtab by section TYPE (synth emits an empty section name).
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name == FUNC:
                    fa = sym["st_value"]
    if fa is None:
        sys.exit(f"{elf}: symbol {FUNC} not found")
    return code, base, fa


def text_bytes(elf):
    return ELFFile(open(elf, "rb")).get_section_by_name(".text").data()


def run_arm(elf, v):
    code, base, fa = load(elf)
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LINMEM & ~0xFFFF, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.reg_write(UC_ARM_REG_R0, v & 0xFFFFFFFF)
    try:
        mu.emu_start((CODE + fa - base) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return {off: int.from_bytes(mu.mem_read(LINMEM + off, 4), "little")
            for off in FIELDS}


def wasm_mem(v):
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WAT, "rb").read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    inst.exports(store)[FUNC](store, v)
    mem = inst.exports(store)["memory"]
    data = mem.read(store, 0, 0x110)
    return {off: int.from_bytes(data[off:off + 4], "little") for off in FIELDS}


def main():
    elfs = {}
    for tag, (cse, extra) in BUILDS.items():
        elf = f"/tmp/volseg543_diff_{tag}.elf"
        compile_elf(elf, cse, extra)
        elfs[tag] = elf

    # Non-vacuity: the byte-shape lattice must hold or we are testing nothing.
    sizes = {tag: len(text_bytes(elf)) for tag, elf in elfs.items()}
    if not sizes["folded"] < sizes["window"]:
        sys.exit(f"VACUOUS: window ({sizes['window']}B) not > folded "
                 f"({sizes['folded']}B) — the range suppressed nothing")
    if not sizes["window"] < sizes["base"]:
        sys.exit(f"VACUOUS: window ({sizes['window']}B) not < base "
                 f"({sizes['base']}B) — the outside folds did not survive")
    if text_bytes(elfs["cover"]) != text_bytes(elfs["base"]):
        sys.exit("FAIL: full-coverage range must fully decline base-CSE "
                 "(cover .text != base .text)")
    print(f".text: base={sizes['base']}B folded={sizes['folded']}B "
          f"window={sizes['window']}B cover={sizes['cover']}B (≡ base)")

    fails = 0
    for v in [0, 1, 22, 0xDEADBEEF, 0x7FFFFFFF, 0xFFFFFFFF]:
        gt = wasm_mem(v)
        line = [f"dma_window({v:#x}):"]
        for tag, elf in elfs.items():
            got = run_arm(elf, v)
            ok = got == gt
            fails += 0 if ok else 1
            line.append(f"{tag}={'ok' if ok else 'MISMATCH'}")
            if not ok:
                line.append(f"\n    {tag}={got}\n    wt ={gt}")
        print(" ".join(line))

    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
