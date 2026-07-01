#!/usr/bin/env python3
"""#538 milestone-1b — validate the aarch64 backend's codegen end-to-end.

Compiles a small integer module with `synth compile -b aarch64`, then executes
each exported function's emitted A64 `.text` under unicorn (UC_ARCH_ARM64) and
diffs the result against wasmtime ground truth. This is the "third backend = third
oracle" property: the same wasm lowered to A64 must compute the same values as it
does in wasmtime (and, by the Thumb-2/RV32 differentials, as on the other
backends).

Runs on any host (unicorn emulates A64); on an arm64 host the same `.text` also
runs natively. NOTE (milestone-1c follow-up): the CLI currently wraps the A64
`.text` in its ARM ELF container (EM_ARM) rather than the backend's EM_AARCH64
relocatable object — this harness reads the `.text` bytes + symbol offsets and is
wrapper-agnostic, so it validates the *codegen*; the backend's own
`compile_module` already emits a correct EM_AARCH64 object (unit-tested in
`crates/synth-backend-aarch64/src/elf.rs`).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/aarch64_add_538_differential.py
"""
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_W1,
    UC_ARM64_REG_W2,
)

WAT = Path(__file__).with_name("aarch64_add_538.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
ARG_REGS = [UC_ARM64_REG_W0, UC_ARM64_REG_W1, UC_ARM64_REG_W2]

CASES = [
    ("add", (2, 3)),
    ("add", (0xFFFFFFFF, 1)),          # wrap
    ("add", (0x7FFFFFFF, 1)),          # signed overflow
    ("muladd", (3, 4, 5)),
    ("muladd", (0xFFFF, 0xFFFF, 0)),   # 32-bit mul truncation
    ("const_sub", (20,)),
    ("const_sub", (0,)),               # 0 - 7 = -7
    ("xor_or", (0b1010, 0b0110)),
]


def wasmtime_run(fn, args):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    return wasmtime.Instance(store, module, []).exports(store)[fn](store, *args)


def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"aarch64 compile failed/skipped: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"] & ~1  # mask any stray low bit
    return code, base, syms


def unicorn_run(code, base, faddr, args):
    off = faddr - base
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    for r, v in zip(ARG_REGS, args):
        mu.reg_write(r, v & 0xFFFFFFFF)
    try:
        mu.emu_start(CODE + off, RET, count=1000)
    except UcError as e:
        return f"ERR:{e}"
    raw = mu.reg_read(UC_ARM64_REG_W0) & 0xFFFFFFFF
    return struct.unpack("<i", struct.pack("<I", raw))[0]


def main():
    out = "/tmp/aarch64_add_538.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    fails = 0
    for fn, args in CASES:
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing")
            fails += 1
            continue
        exp = wasmtime_run(fn, args)
        got = unicorn_run(code, base, syms[fn], args)
        ok = isinstance(got, int) and (got & 0xFFFFFFFF) == (exp & 0xFFFFFFFF)
        if not ok:
            fails += 1
        print(f"{'OK ' if ok else 'BUG'} {fn}{args} A64={got} wasmtime={exp}")
    print("\nRESULT:", "PASS — aarch64 codegen matches wasmtime (third oracle)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
