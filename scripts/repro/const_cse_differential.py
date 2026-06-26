#!/usr/bin/env python3
"""VCR-RA const-CSE (#242) — EXECUTION-validate the optimized-path const cache.

The optimized (non-`--relocatable`) ARM path re-materializes a constant at every
use: the same `i32.const N` becomes a fresh `movw`/`movt` (or `mov`) each time.
gale measured this on silicon — flat_flight spends 61% of its const
materializations on values already sitting in a register. `SYNTH_CONST_CSE=1`
turns on a pressure-neutral const cache (`optimizer_bridge.rs`): when the wanted
value already lives in a still-valid register, the new vreg is ALIASED to that
register and nothing is emitted. The cache is reconstructed from the EMITTED ARM
at the top of each lowering step (so it survives the many `continue` arms) and
RESET at every control-flow boundary (an unmodeled `reg_effect` op), confining
reuse to straight-line segments.

This is byte-CHANGING codegen, so the flag ships DEFAULT-OFF (off ⇒ byte-identical,
the frozen gate proves it). This harness is the correctness oracle for the
flag-ON path: it compiles `const_cse.wat` with `SYNTH_CONST_CSE=1` via the
optimized path, runs each export under unicorn (UC_ARCH_ARM / Thumb), and asserts
the returned value is bit-identical to wasmtime ground truth across a spread of
inputs (including negatives and zero). Covered shapes (see the .wat header):
large/small/negative/mixed consts, reuse ACROSS an if/else (cache must reset),
and a 12-live-local function that forces real spills (proves an aliased register
is still correct after it is itself spilled — STR is a use, not a def). It also
reports the instruction-count delta off-vs-on as information (no gate — the win
is real where there's register headroom and inert under pressure, never a
regression).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/const_cse_differential.py
Exits nonzero on any value mismatch.
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
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("const_cse.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, STK, RET = 0x100000, 0x900000, 0x300000
EXPORTS = ["large3", "small3", "neg", "mixed", "ctrl", "spill12"]
INPUTS = [5, 0, -3, 1000, -100000, 7]


def wasmtime_run(fn, arg):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, arg)


def compile_optimized(out, cse_on):
    env = {"PATH": "/usr/bin:/bin"}
    if cse_on:
        env["SYNTH_CONST_CSE"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (cse_on={cse_on}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


def unicorn_run(code, base, faddr, arg):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, 0x20000000)
    mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    raw = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    return struct.unpack("<i", struct.pack("<I", raw))[0]


def insn_count(code):
    # Rough Thumb instruction count: a halfword whose top 5 bits are 0b11101..
    # 0b11111 starts a 32-bit instruction; otherwise it is a 16-bit instruction.
    n, i = 0, 0
    while i + 2 <= len(code):
        hw = code[i] | (code[i + 1] << 8)
        wide = (hw >> 11) >= 0b11101
        i += 4 if wide else 2
        n += 1
    return n


def main():
    off_elf, on_elf = "/tmp/const_cse_off.elf", "/tmp/const_cse_on.elf"
    compile_optimized(off_elf, cse_on=False)
    compile_optimized(on_elf, cse_on=True)
    off_code, off_base, off_syms = load(off_elf)
    on_code, on_base, on_syms = load(on_elf)

    fails = 0
    for fn in EXPORTS:
        faddr = on_syms.get(fn)
        if faddr is None:
            print(f"FAIL {fn}: symbol missing")
            fails += 1
            continue
        for arg in INPUTS:
            exp = wasmtime_run(fn, arg)
            got = unicorn_run(on_code, on_base, faddr, arg)
            ok = isinstance(got, int) and got == exp
            if not ok:
                fails += 1
            print(f"{'OK  ' if ok else 'FAIL'} {fn} cse-on({arg}) = {got} "
                  f"(wasmtime {exp})")

    print("\n--- instruction-count delta (information, not a gate) ---")
    off_n, on_n = insn_count(off_code), insn_count(on_code)
    print(f".text Thumb instructions: off={off_n}  on={on_n}  "
          f"delta={off_n - on_n} ({'fewer with CSE' if on_n < off_n else 'no change'})")

    print("\nRESULT:", "PASS" if not fails else f"FAIL ({fails} mismatches)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
