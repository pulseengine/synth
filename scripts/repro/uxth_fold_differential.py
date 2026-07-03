#!/usr/bin/env python3
"""VCR-RA uxth/uxtb fold validation oracle (#428, epic #242).

The fold rewrites `movw rM,#0xffff; and rD,rN,rM` -> `uxth rD,rN` (and the 0xff /
uxtb form), dropping the dead movw. `uxth` zero-extends the low halfword, i.e.
`rN & 0xffff` — exactly what the AND computes — so the result must be identical.

wasmtime is ground truth; unicorn runs synth's ARM (`--relocatable` path). This
harness compiles `uxth_fold.wat` BOTH ways — flag-off (SYNTH_NO... clean, the
shipped lowering) and flag-on (SYNTH_UXTH_FOLD=1, with the fold) — and asserts
flag-off == flag-on == wasmtime over a vector sweep. flag-on must also actually
fold (the fold is non-vacuous on this fixture: 2 uxth folds).

Run (venv with wasmtime+unicorn+capstone+pyelftools, e.g. /tmp/armv):
  /tmp/armv/bin/python scripts/repro/uxth_fold_differential.py
"""

import re
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = "scripts/repro/uxth_fold.wat"
SYNTH = "./target/debug/synth"

CODE, LIN, STK, RET = 0x200000, 0x40000, 0x180000, 0x300000

VECTORS = [
    (0, 0, 0),
    (1, 2, 3),
    (0xFFFF, 0xFFFF, 0xFF),
    (0x12345678, 0xABCDEF01, 0x99),
    (0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF),
    (0x0001FFFF, 0x7FFF8000, 0x100),
    (0xDEADBEEF, 0xCAFEBABE, 0x42),
]


def compile_variant(fold_on):
    elf = f"/tmp/uxth_{'on' if fold_on else 'off'}.elf"
    # DEFAULT-ON since the #242 flag-audit flip-wave: "on" is the shipped
    # default, "off" is the `SYNTH_UXTH_FOLD=0` opt-out (pre-flip lowering).
    env = {"PATH": "/usr/bin:/bin"}
    env["SYNTH_UXTH_FOLD"] = "1" if fold_on else "0"
    env["SYNTH_FUSE_STATS"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", WAT, "-o", elf, "--target", "cortex-m4",
         "--relocatable", "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    assert r.returncode == 0, f"compile (fold={fold_on}) failed: {r.stderr}"
    folds = 0
    m = re.search(r"\[uxth-fold\] (\d+) ", r.stderr)
    if m:
        folds = int(m.group(1))
    return elf, folds


def fn_addr_and_code(elf):
    dis = subprocess.run([SYNTH, "disasm", elf], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r"^([0-9a-f]{8}) <(\w+)>:", dis, re.M)}
    fa = syms.get("func_0") or syms.get("pack")
    text = ELFFile(open(elf, "rb")).get_section_by_name(".text")
    return fa, text.data(), text["sh_addr"]


def arm(elf, a, b, c):
    fa, code, base = fn_addr_and_code(elf)
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, b & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R2, c & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + fa - base) | 1, RET, count=10000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    off_elf, off_folds = compile_variant(False)
    on_elf, on_folds = compile_variant(True)
    assert off_folds == 0, f"flag-off must not fold (got {off_folds})"
    assert on_folds >= 1, f"flag-on must fold (non-vacuous); got {on_folds}"
    print(f"folds: flag-off={off_folds}  flag-on={on_folds}")

    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, wasmtime.wat2wasm(open(WAT).read()))

    def wt(a, b, c):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)["pack"](store, a, b, c) & 0xFFFFFFFF

    fails = 0
    for (a, b, c) in VECTORS:
        gt = wt(a, b, c)
        off = arm(off_elf, a, b, c)
        on = arm(on_elf, a, b, c)
        ok = isinstance(off, int) and isinstance(on, int) and off == gt and on == gt
        fails += 0 if ok else 1
        print(f"pack(0x{a:08X},0x{b:08X},0x{c:08X}) off={off if isinstance(off,str) else f'0x{off:08X}'}"
              f" on={on if isinstance(on,str) else f'0x{on:08X}'}  (wasmtime 0x{gt:08X})"
              f"{'' if ok else '  <-- MISMATCH'}")
    print(f"\n{len(VECTORS) - fails}/{len(VECTORS)} match (flag-off == flag-on == wasmtime)")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
