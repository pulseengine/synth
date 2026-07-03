#!/usr/bin/env python3
"""#499 — EXECUTION-validate optimized-path spill-frame teardown on return.

The optimized (non-`--relocatable`) ARM path allocates a spill frame
(`sub sp,#N`) when the flag-off `Opcode::Const` oldest-vreg eviction spill
fires under register pressure, but the frame teardown (`add sp,#N`) was only
inserted before returns that ALREADY existed in the body. The common wasm
shape — a function that falls off its end, whose return is APPENDED by the
bridge — got a bare return: SP came back off by N. Post-#490 the epilogue is
`pop {r4-r8,pc}`, which READS the return address through SP → PC is popped
from a spill slot → crash (unicorn: UC_ERR_FETCH_UNMAPPED). Reachable
straight-line AND under control flow (the original #499 shape).

This harness compiles `spill_frame_499.wat` (minimal straight-line
`min_fields` + control-flow `nested`, both branch directions) and
`redundant_base_materialization.wat::init_fields` (the #592 flip-wave
reproducer) via the optimized path with `SYNTH_BASE_CSE=0` (default-on
base-CSE post-#592 relieves the pressure and would make the oracle vacuous),
then runs each function under unicorn (UC_ARCH_ARM / Thumb) and asserts:

  1. the function actually carries a spill frame (`sub.w sp,sp,#imm` present
     in its body) — non-vacuity tripwire: if a future lever removes the
     pressure, refresh the fixture instead of green-washing;
  2. execution reaches the return trampoline (no fault, PC == ret);
  3. SP is balanced on return (== its entry value);
  4. linear MEMORY is bit-identical to wasmtime ground truth.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/spill_frame_499_differential.py
Exits nonzero on any mismatch.
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
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_SP,
)

REPRO = Path(__file__).parent
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
# Absolute linear-memory base the optimized (non-relocatable) path materializes
# for a const address: `movw ip,#0x100; movt ip,#0x2000` → 0x20000100 (see #197).
LINMEM = 0x20000100
MEM_WINDOW = 64  # bytes of memory compared against ground truth
SP_INIT = 0x98000

# (wat file, function, [arg lists — empty tuple = no args])
CASES = [
    ("spill_frame_499.wat", "min_fields", [()]),
    ("spill_frame_499.wat", "nested", [(0,), (1,)]),
    ("redundant_base_materialization.wat", "init_fields", [()]),
]


def compile_optimized(wat, out):
    env = {"PATH": "/usr/bin:/bin", "SYNTH_BASE_CSE": "0"}
    r = subprocess.run(
        [SYNTH, "compile", str(wat), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env=env,
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


def func_body(code, base, syms, func):
    """Bytes of `func` from its symbol to the next symbol (or .text end).
    Thumb function symbols carry bit 0 set — mask it off."""
    start = (syms[func] & ~1) - base
    ends = sorted((v & ~1) - base for v in syms.values() if (v & ~1) - base > start)
    end = ends[0] if ends else len(code)
    return code[start:end]


def has_spill_frame(body):
    """True if the body contains `sub.w sp,sp,#imm` (T32: f1ad 0dxx,
    little-endian bytes: ad f1 xx 0d)."""
    for i in range(len(body) - 3):
        if body[i] == 0xAD and body[i + 1] == 0xF1 and body[i + 3] == 0x0D:
            return True
    return False


def wasm_mem(wat, func, args):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wat.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    inst.exports(st)[func](st, *args)
    return bytes(inst.exports(st)["memory"].read(st, 0, MEM_WINDOW))


def run_arm(code, base, addr, args):
    """Returns (mem, err): err is a failure string or None."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(LINMEM & ~0xFFFF, 0x20000)  # page-aligned region covering LINMEM
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    if args:
        mu.reg_write(UC_ARM_REG_R0, args[0] & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, SP_INIT)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        mu.emu_start(addr | 1, ret, timeout=5_000_000)
    except UcError as e:
        return None, f"execution fault: {e} (PC=0x{mu.reg_read(UC_ARM_REG_PC):x})"
    pc = mu.reg_read(UC_ARM_REG_PC)
    if pc != ret:
        return None, f"never returned: stopped at PC=0x{pc:x} (want 0x{ret:x})"
    sp = mu.reg_read(UC_ARM_REG_SP)
    if sp != SP_INIT:
        return None, (
            f"SP imbalanced on return: 0x{sp:x} (entry 0x{SP_INIT:x}, "
            f"leak {SP_INIT - sp:+d} bytes) — the #499 missing `add sp`"
        )
    return bytes(mu.mem_read(LINMEM, MEM_WINDOW)), None


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")

    fails = 0
    for wat_name, func, arg_lists in CASES:
        wat = REPRO / wat_name
        elf = f"/tmp/spill_frame_499_{wat.stem}.elf"
        compile_optimized(wat, elf)
        code, base, syms = load(elf)

        if func not in syms:
            print(f"FAIL {func}: symbol missing from {elf}")
            fails += 1
            continue
        if not has_spill_frame(func_body(code, base, syms, func)):
            print(
                f"FAIL {func}: no `sub.w sp,sp,#imm` spill frame in body — "
                "the fixture no longer exercises the #499 teardown path; "
                "refresh the shape instead of shipping a vacuous oracle"
            )
            fails += 1
            continue

        for args in arg_lists:
            label = f"{func}{args if args else '()'}"
            gt = wasm_mem(wat, func, args)
            got, err = run_arm(code, base, syms[func], args)
            if err is not None:
                print(f"FAIL {label}: {err}")
                fails += 1
                continue
            if got != gt:
                diff = [(i, gt[i], got[i]) for i in range(MEM_WINDOW) if gt[i] != got[i]]
                print(f"FAIL {label}: mem diffs (off, wasmtime, synth): {diff}")
                fails += 1
                continue
            print(f"OK   {label}")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
