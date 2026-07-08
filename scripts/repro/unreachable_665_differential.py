#!/usr/bin/env python3
"""#665 — `unreachable` must TRAP (WASM Core §4.4.5), on BOTH ISAs.

synth compiled wasm `unreachable` to a NO-OP: the decoder dropped it as
"intentionally ignorable" (`wasm_decoder.rs` lumped it with Nop), so no backend
ever received the op — control fell through every panic!/abort/exhaustiveness
guard and returned undefined register state. The selector trap arms (ARM:
`UDF #0`, RV32: `ebreak`) already existed; this harness proves they now fire.

Functions (scripts/repro/unreachable_665.wat):
  - boom(x,y)      body is `unreachable`      -> must trap on entry
  - guarded(x)     if x>=0 then 1 else unreachable
  - guarded_br(x)  block + br_if guard, `unreachable` in the dead-end

Oracle, per ISA under unicorn, vs wasmtime ground truth:
  - the trap cases MUST fault (unicorn exception), like wasmtime traps;
  - the guarded positive direction MUST return 1 normally (NON-VACUITY: the
    emitted trap instruction cannot break the live path).

RED on pre-fix synth: boom/guarded fall through and "return" garbage instead
of faulting. On RV32, `guarded` (if/else-with-result whose else arm is
`unreachable`) currently LOUD-DECLINES (#343 arity check) — the symbol is
absent, which the contract allows (trap or loud-decline, never fall-through);
the harness accepts absence for that one function on RV32 and prints it.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/unreachable_665_differential.py
Exits nonzero on any fall-through/mismatch.
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_ARCH_RISCV, UC_MODE_RISCV32, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = Path(__file__).with_name("unreachable_665.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
TRAP = "TRAP"
LINMEM = 0x20000100  # optimized-path absolute linear-memory base (#197)

# function -> [(args, expected)]; expected is a value or TRAP.
CASES = [
    ("boom", (7, 9), TRAP),
    ("guarded", (5,), 1),  # non-vacuity: live path still returns
    ("guarded", (-5,), TRAP),
    ("guarded_br", (5,), 1),
    ("guarded_br", (-5,), TRAP),
]
# RV32 loud-declines this function today (#343 if/else result-arity check on
# an else arm that is pure `unreachable`) — absence is an acceptable outcome
# there; presence must then trap like everywhere else.
RV32_MAY_DECLINE = {"guarded"}


def compile_elf(out, backend_args):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, *backend_args, "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    if r.returncode != 0:
        sys.exit(f"compile failed ({backend_args}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] - base
    return code, base, syms


def wasm_expected(func, args):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    try:
        return inst.exports(st)[func](st, *args) & 0xFFFFFFFF
    except Exception:
        return TRAP


def run_arm(code, fa, args):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(0, 0x20000)
    mu.mem_write(0, code)
    mu.mem_map(LINMEM & ~0xFFFF, 0x20000)
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
        mu.reg_write(reg, val & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R11, LINMEM)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        mu.emu_start((fa & ~1) | 1, ret, timeout=5_000_000, count=10_000)
    except UcError:
        return TRAP  # UDF #0 -> undefined-instruction exception
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def run_rv(code, fa, args):
    CODE, STK, RET = 0x100000, 0x90000, 0x200000
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LINMEM & ~0xFFFF, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    for reg, val in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1), args):
        mu.reg_write(reg, val & 0xFFFFFFFF)
    mu.reg_write(UC_RISCV_REG_SP, STK)
    mu.reg_write(UC_RISCV_REG_S11, LINMEM)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + fa, RET, timeout=5_000_000, count=10_000)
    except UcError:
        return TRAP  # ebreak -> breakpoint exception
    return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    arm_elf, rv_elf = "/tmp/unr665_arm.elf", "/tmp/unr665_rv.o"
    compile_elf(arm_elf, ["-b", "arm", "--target", "cortex-m4"])
    compile_elf(rv_elf, ["-b", "riscv", "-t", "rv32imac", "--relocatable"])
    arm = load(arm_elf)
    rv = load(rv_elf)

    fails = 0
    for func, args, expected in CASES:
        gt = wasm_expected(func, args)
        if gt != expected:
            sys.exit(f"harness bug: wasmtime {func}{args} = {gt}, expected {expected}")
        for isa, (code, _base, syms), runner in (
            ("thumb2", arm, run_arm),
            ("rv32", rv, run_rv),
        ):
            if func not in syms:
                if isa == "rv32" and func in RV32_MAY_DECLINE:
                    print(f"note {isa:6} {func}{args}: loud-declined (absent) — allowed")
                    continue
                fails += 1
                print(f"FAIL {isa:6} {func}{args}: SYMBOL MISSING from ELF symtab")
                continue
            got = runner(code, syms[func], args)
            ok = got == gt
            fails += 0 if ok else 1
            print(f"{'OK  ' if ok else 'FAIL'} {isa:6} {func}{args}: "
                  f"synth={got} wasmtime={gt}")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
