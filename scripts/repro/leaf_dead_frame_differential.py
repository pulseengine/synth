#!/usr/bin/env python3
"""VCR-RA-002 / VCR-ORACLE-001 (#390, #242) — EXECUTION-validate dead-frame elision.

`compute_local_layout` reserves a frame slot (`sub sp,#N` / `add sp,#N`) for every
non-param wasm local. Local promotion (v0.14.0) then homes the eligible i32 locals
in registers, leaving those frame bytes never accessed — a dead `sub`/`add sp` pair.
`elide_dead_frame` (SYNTH_DEAD_FRAME_ELIM=1) removes it when the body provably never
touches SP.

This harness runs `leaf3` under unicorn in BOTH the flag-off build (frame present)
and the flag-on build (frame elided) and asserts both equal wasmtime ground truth
across an input sweep. Because the transform deletes SP arithmetic, the danger it
guards against is precisely a SILENT stack imbalance — so executing both builds and
comparing the returned value (and that the function returns cleanly via the popped
LR) is the oracle that matters, not a byte diff alone.

NON-VACUITY: the run aborts unless the flag-on .text is strictly smaller than
flag-off (the `sub`/`add sp` pair was actually removed) — otherwise nothing was
transformed and the "validation" is theater.

leaf3(p) = a=p+1; b=a+2; c=b+3; (a+b)+(c+p) = 4*p + 10  (mod 2^32)

Run (needs wasmtime + unicorn + pyelftools, e.g. a venv):
  python scripts/repro/leaf_dead_frame_differential.py

Exits nonzero on any mismatch or vacuity failure.
"""
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WASM = "scripts/repro/leaf_caller_saved.wat"
SYNTH = "./target/debug/synth"
ELF_OFF, ELF_ON = "/tmp/leaf_frame_off.elf", "/tmp/leaf_frame_on.elf"
CODE, LIN, STK, RET = 0x200000, 0x40000, 0x90000, 0x300000

# p values: signed edges, i32-wrap (4p+10 overflow), zero.
VECTORS = [0, 1, 7, 100, -1, -3, 2147483647, -2147483648, 1073741823, 12345]


def to_s32(x):
    x &= 0xFFFFFFFF
    return x - 0x100000000 if x & 0x80000000 else x


def compile_elf(out, elide):
    env = {"PATH": "/usr/bin:/bin"}
    if elide:
        env["SYNTH_DEAD_FRAME_ELIM"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", WASM, "-o", out, "--target", "cortex-m4",
         "--all-exports", "--relocatable", "--native-pointer-abi"],
        capture_output=True, text=True, env={**env},
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (elide={elide}): {r.stderr}")


def load(elf):
    # leaf3 is the only function → .text offset 0; entry == CODE.
    text = ELFFile(open(elf, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    if not code:
        sys.exit(f"{elf}: .text is empty")
    return code, base, base


def run_arm(code, base, fa, p):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_R0, p & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + fa - base) | 1, RET, count=10000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    compile_elf(ELF_OFF, elide=False)
    compile_elf(ELF_ON, elide=True)

    off = load(ELF_OFF)
    on = load(ELF_ON)

    # Non-vacuity: the frame `sub`/`add sp` pair (two 4-byte wide insns) must
    # actually be gone — flag-on .text strictly smaller than flag-off.
    off_len, on_len = len(off[0]), len(on[0])
    if not on_len < off_len:
        sys.exit(f"VACUOUS: flag-on .text ({on_len}B) not smaller than "
                 f"flag-off ({off_len}B) — no frame was elided")

    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())

    def wt(p):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)["leaf3"](store, p) & 0xFFFFFFFF

    fails = 0
    for p in VECTORS:
        gt = wt(p)
        r_off = run_arm(*off, p)
        r_on = run_arm(*on, p)
        ok = isinstance(r_off, int) and isinstance(r_on, int) and r_off == gt and r_on == gt
        fails += 0 if ok else 1
        so = f"0x{r_off:08X}" if isinstance(r_off, int) else r_off
        sn = f"0x{r_on:08X}" if isinstance(r_on, int) else r_on
        print(f"leaf3({p}) off={so} on={sn} wasmtime=0x{gt:08X}"
              f"{'' if ok else '  <-- MISMATCH'}")

    print(f"\n{len(VECTORS) - fails}/{len(VECTORS)} match (off==on==wasmtime); "
          f"frame elided: {off_len}B -> {on_len}B (-{off_len - on_len}B)")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
