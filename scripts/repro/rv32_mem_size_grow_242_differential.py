#!/usr/bin/env python3
"""#223 / #242 (VCR-SEL-005) — RV32 memory.size / memory.grow execution oracle.

The v0.49 cross-backend op-parity gate ledgered `memory.size` and `memory.grow`
as ARM-lowers / RV32-declines gaps. This lane lowers both on RV32:

  * `memory.size`  — FIXED-memory page count, materialized as a compile-time
    constant (`li rd, linear_memory_bytes / 65536`). No runtime size register
    (the RV analogue of ARM's R10) is needed because the size cannot change.
  * `memory.grow`  — fixed memory cannot grow, so return `-1` (WASM's "grow
    failed" sentinel). The legal `memory.grow(0)` "return current size" idiom
    (WASM Core §4.4.7) is folded to `memory.size` up front by the SHARED
    `synth_core::rewrite_memory_grow_zero` (ARM+RV32), so `grow(0)` never
    reports failure — that is the whole soundness point of this differential.

This is the EXECUTION half of moving those two ops off the parity allowlist.
It compiles a real module with a `(memory 3)` section on RV32, runs each export
under unicorn with `s11 = __linear_memory_base`, and checks:

  - `sz`     == 3   (current pages; == wasmtime)
  - `grow0`  == 3   (grow-by-0 returns current size — the shared fold; == wasmtime)
  - `grow2`  == -1  (grow-by->0 on FIXED memory returns -1; this is the sound,
                     documented behavior and legitimately DIFFERS from wasmtime,
                     whose memory can actually grow — so grow>0 is asserted
                     DIRECTLY, not against wasmtime, mirroring mem_grow_539)

`sz`/`grow0` are cross-checked against wasmtime with a FRESH instance per call
(memory.grow mutates the store; a shared instance would pollute the oracle).

A LOUD failure (never a skip) on a missing tool — a gate that skips on an
assumption is vacuous.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/rv32_mem_size_grow_242_differential.py
"""
import os
import struct
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import UC_RISCV_REG_A0, UC_RISCV_REG_RA, UC_RISCV_REG_S11, UC_RISCV_REG_SP

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000
PAGES = 3

# A module with a fixed 3-page memory. `sz` reads the page count; `grow0` is the
# legal grow-by-0 idiom (must return current size); `grow2` grows by 2 (fixed
# memory: -1).
WAT = """(module
  (memory 3)
  (func (export "sz") (result i32) memory.size)
  (func (export "grow0") (result i32) i32.const 0 memory.grow)
  (func (export "grow2") (result i32) i32.const 2 memory.grow))"""


def wasmtime_run(module, engine, fn):
    # FRESH instance per call: memory.grow mutates the store.
    store = wasmtime.Store(engine)
    return wasmtime.Instance(store, module, []).exports(store)[fn](store)


def compile_rv32(wat_path, out):
    cmd = [SYNTH, "compile", wat_path, "-o", out, "-b", "riscv",
           "-t", "rv32imac", "--all-exports", "--relocatable"]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0 or "skipping" in (r.stdout + r.stderr):
        print(f"RV32 mem-size/grow ORACLE: FAIL — compile failed/skipped:\n{r.stdout}{r.stderr}")
        sys.exit(1)


def load(elf):
    # Read function offsets from the ELF SYMBOL TABLE (host-independent), NOT by
    # parsing `synth disasm` TEXT — disasm formatting is host-dependent and the
    # regex matched nothing on the Linux CI runner (empty syms → "no symbol"),
    # even though it matched on macOS. See the differential-harness symtab lesson.
    ef = ELFFile(open(elf, "rb"))
    text_idx = ef.get_section_index(".text")
    code = ef.get_section_by_name(".text").data()
    symtab = ef.get_section_by_name(".symtab")
    if symtab is None:
        print("RV32 mem-size/grow ORACLE: FAIL — ELF has no .symtab")
        sys.exit(1)
    # In a --relocatable object a function symbol's st_value is its offset within
    # .text — exactly the `faddr` unicorn_run expects (CODE + faddr).
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols()
            if s.name and s["st_shndx"] == text_idx}
    return code, syms


def unicorn_run(code, faddr):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, PAGES * 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_RISCV_REG_SP, STK)
    mu.reg_write(UC_RISCV_REG_S11, LIN)  # s11 = __linear_memory_base
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + faddr, RET, count=2000)
    except UcError as e:
        return f"ERR:{e}"
    raw = mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
    return struct.unpack("<i", struct.pack("<I", raw))[0]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.encode())

    # (export, expected). grow2 is asserted to -1 DIRECTLY (fixed memory cannot
    # grow — sound behavior that differs from wasmtime, which can grow).
    cases = [
        ("sz", wasmtime_run(module, engine, "sz")),        # 3
        ("grow0", wasmtime_run(module, engine, "grow0")),  # 3 — shared fold
        ("grow2", -1),                                     # fixed-mem: -1
    ]

    d = tempfile.mkdtemp(prefix="rv32_memsg_")
    wat = os.path.join(d, "m.wat")
    open(wat, "w").write(WAT)
    out = os.path.join(d, "m.o")
    compile_rv32(wat, out)
    code, syms = load(out)

    fails = 0
    for fn, expect in cases:
        faddr = syms.get(f"func_{['sz', 'grow0', 'grow2'].index(fn)}") or syms.get(fn)
        if faddr is None:
            print(f"RV32 mem-size/grow ORACLE: FAIL — no symbol for export {fn} ({sorted(syms)})")
            sys.exit(1)
        got = unicorn_run(code, faddr)
        ok = got == expect
        fails += 0 if ok else 1
        note = "" if fn != "grow2" else "  (fixed-mem: -1 is sound; wasmtime grows)"
        print(f"{'OK ' if ok else 'BUG'} {fn:6} synth={got} expect={expect}{note}")

    print("\nRV32 mem-size/grow ORACLE: PASS — memory.size + memory.grow (+ grow(0) fold) "
          "execute correctly on RV32" if not fails else f"RV32 mem-size/grow ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
