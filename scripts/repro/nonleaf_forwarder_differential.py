#!/usr/bin/env python3
"""VCR-RA non-leaf prologue lever (#428, epic #242) — EXECUTION-validate it.

`SYNTH_NONLEAF_PROLOGUE=1` relaxes the dead-frame elision AND the callee-saved
save-set shrink to fire across a DIRECT call, so a thin forwarder's
`push {r4-r8,lr}; sub sp,#N; ...; bl; ...; add sp,#N; pop {r4-r8,pc}` collapses to
`push {r4,lr}; ...; bl; ...; pop {r4,pc}` (gale's driver-class residual). It is a
cycle/stack win, not a size win for the push alone (`push` is one instruction
either way) — but the frame removal also drops the `sub`/`add sp`. The pass runs
on the optimized path, which has no cargo byte-gate, so EXECUTION is the oracle:
this harness runs each fixture function under unicorn in BOTH flag states and
asserts (a) the result equals wasmtime ground truth, and (b) the caller's
callee-saved registers (r4-r8) are preserved — the property the save-set shrink
must not break.

NON-VACUITY (asserted independently, per the lever's two halves):
  * frame gone   — flag-on `.text` is strictly smaller (the `sub`/`add sp` pair).
  * prologue gone — `tick`'s prologue BYTES differ flag-off vs flag-on (the push
                    register-list shrank); flag-off keeps the 32-bit `push
                    {r4-r8,lr}` (`e92d…`), flag-on emits the 16-bit `push {r4,lr}`.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/nonleaf_forwarder_differential.py
Exits nonzero on any mismatch or vacuity failure.
"""
import os
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R4,
    UC_ARM_REG_R5,
    UC_ARM_REG_R6,
    UC_ARM_REG_R7,
    UC_ARM_REG_R8,
    UC_ARM_REG_SP,
)

WAT = "scripts/repro/nonleaf_forwarder.wat"
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, STK, RET = 0x100000, 0x180000, 0x200000
# Callee-saved sentinels the forwarder must preserve across its shrunk prologue.
SENTINELS = {
    UC_ARM_REG_R4: 0x4444_4444,
    UC_ARM_REG_R5: 0x5555_5555,
    UC_ARM_REG_R6: 0x6666_6666,
    UC_ARM_REG_R7: 0x7777_7777,
    UC_ARM_REG_R8: 0x8888_8888,
}
CASES = ["tick", "tick_two"]


def compile_elf(out, nonleaf):
    env = {"PATH": "/usr/bin:/bin"}
    if nonleaf:
        env["SYNTH_NONLEAF_PROLOGUE"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", WAT, "-o", out, "-b", "arm", "--target", "cortex-m4",
         "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (nonleaf={nonleaf}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] - base  # keep Thumb bit
    return code, base, syms


def run_arm(code, base, fa, args):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    for i, p in enumerate(args):
        mu.reg_write(UC_ARM_REG_R0 + i, p & 0xFFFFFFFF)
    for r, v in SENTINELS.items():
        mu.reg_write(r, v)
    # fa carries the Thumb bit; place it relative to CODE (PC-relative BL works
    # at any load base, but symbol offsets are .text-relative so subtract base).
    entry = CODE + (fa & ~1) - base
    try:
        mu.emu_start(entry | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}", False
    res = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    preserved = all((mu.reg_read(r) & 0xFFFFFFFF) == v for r, v in SENTINELS.items())
    return res, preserved


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    off_elf, on_elf = "/tmp/nlf_off.o", "/tmp/nlf_on.o"
    compile_elf(off_elf, False)
    compile_elf(on_elf, True)
    off_code, off_base, off_syms = load(off_elf)
    on_code, on_base, on_syms = load(on_elf)

    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WAT, "rb").read())

    def wt(func):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[func](store) & 0xFFFFFFFF

    fails = 0
    for func in CASES:
        gt = wt(func)
        r_off, p_off = run_arm(off_code, off_base, off_syms[func], [])
        r_on, p_on = run_arm(on_code, on_base, on_syms[func], [])
        ok = (r_off == gt and r_on == gt and p_off and p_on)
        fails += 0 if ok else 1
        tag = "" if ok else "  <-- FAIL"
        print(f"{func}(): off={r_off} on={r_on} wt={gt} "
              f"callee-saved-preserved off={p_off} on={p_on}{tag}")

    # NON-VACUITY 1: the frame removal shrinks .text.
    off_len, on_len = len(off_code), len(on_code)
    if not on_len < off_len:
        print(f"VACUOUS: flag-on .text ({on_len}B) not < flag-off ({off_len}B) "
              "— dead frame not removed")
        fails += 1
    # NON-VACUITY 2: tick's prologue bytes changed (the push reg-list shrank).
    to_off, to_on = off_syms["tick"] & ~1, on_syms["tick"] & ~1
    pro_off = off_code[to_off - off_base: to_off - off_base + 4]
    pro_on = on_code[to_on - on_base: to_on - on_base + 4]
    if pro_off == pro_on:
        print(f"VACUOUS: tick prologue unchanged ({pro_off.hex()}) — push not shrunk")
        fails += 1
    else:
        print(f"\ntick prologue: off={pro_off.hex()} -> on={pro_on.hex()} (push shrank); "
              f".text {off_len}B -> {on_len}B (-{off_len - on_len}B, frames removed)")

    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
