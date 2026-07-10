#!/usr/bin/env python3
"""#681 — T3 ADD.W raw-immediate packing: dynamic base + static offset 0x100..0xFFF.

`encode_thumb32_add_imm` packed the raw offset into the T3 ADD.W ThumbExpandImm
field (a MODIFIED immediate, correct only for imm <= 0xFF). Dynamic-address
load/store with a static offset in [256, 4095] silently accessed the wrong
address: ThumbExpandImm(0x100)=0, ThumbExpandImm(0x200)=0,
ThumbExpandImm(0x400)=0x8000_0000. Fix: ADDW (T4, plain imm12) for
0x100..=0xFFF — the lowering `encode_thumb32_add` already used per #253.

Cases (wasmtime ground truth, unicorn Thumb-2 with R11 = linmem base,
R10 = mem size in bytes):

  probe(base)   — store+load-back at offsets {0,256,512,1020,1024,4092}
                  RED pre-fix: 256/512/1024 stores land at base+0; the
                  offset-1024 access faults 2 GiB past the base (UC_ERR).
  clobber(base) — gale's exact repro: offset=512 store must not clobber
                  base+0 (pre-fix returns 4660, correct 111).
  subword(base) — i8/i16 store+load at offsets 257/770 (scalar sub-word arms).
  wide(base)    — i64 store+load at offset 768 (i64_effective_base path).

Variants: --safety-bounds none and software, both --relocatable (the direct
selector emits reg-offset Ldr/Str with a static offset — the #382 paths that
call encode_thumb32_add_imm). The software variant is the BOUNDS-BYPASS pin:
pre-fix the guard (correct T4 ADDW) checks the intended address while the
access uses the mis-encoded one, so an in-bounds base passes the check yet the
access escapes the checked region. An OOB base must trap in BOTH wasmtime and
synth (guard UDF) — trap-to-trap counts as a match.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/addw_offset_681_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("addw_offset_681.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

CODE = 0x1000
LIN = 0x200000  # linear memory base (R11)
MEM_BYTES = 0x10000  # 1 wasm page
STK = 0x3F000
RET = 0x30000

FUNCS = ["probe", "clobber", "subword", "wide"]
# In-bounds bases (max static offset is 4092+4 -> base <= 0xEF00 is safe).
BASES = [0, 4, 256, 0x1000, 0x8000, 0xEF00]
# OOB base: 0xFC00 + 4092 + 4 > 0x10000 -> wasmtime traps; synth software
# mode must UDF (trap-to-trap match). Only meaningful for `probe`.
OOB_BASES = [0xFC00]

VARIANTS = [
    ("none", ["-t", "cortex-m3", "--relocatable", "--safety-bounds", "none"]),
    ("software", ["-t", "cortex-m3", "--relocatable", "--safety-bounds", "software"]),
]

TRAP = "TRAP"


def compile_elf(out, extra):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, *extra, "--all-exports"],
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed ({extra}): {r.stderr}")


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
    return code, syms


def wasm_expected(func, base):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    try:
        return inst.exports(st)[func](st, base) & 0xFFFFFFFF
    except wasmtime.Trap:
        return TRAP


def run_arm(code, off, base):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(0, 0x40000)
    mu.mem_map(LIN, MEM_BYTES)
    mu.mem_write(CODE, code)
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_R0, base & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + off) | 1, RET, timeout=5_000_000, count=100_000)
    except UcError as e:
        # A UDF-triggered stop is the software-mode bounds trap; any other
        # fault (e.g. unmapped 2 GiB-away access) is a miscompile signal.
        # Unicorn reports both as UcError — disambiguate via PC: inside the
        # code region == deliberate trap instruction reached.
        return f"UC_ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    fails = 0
    for vname, extra in VARIANTS:
        with tempfile.NamedTemporaryFile(suffix=".o") as tf:
            compile_elf(tf.name, extra)
            code, syms = load(tf.name)
            cases = [(f, b) for f in FUNCS for b in BASES]
            if vname == "software":
                cases += [("probe", b) for b in OOB_BASES]
            for func, base in cases:
                want = wasm_expected(func, base)
                if func not in syms:
                    print(f"[{vname}] SYMBOL MISSING: {func}")
                    fails += 1
                    continue
                got = run_arm(code, syms[func], base)
                if want == TRAP:
                    # trap-to-trap: synth's software guard hits UDF -> UcError
                    ok = isinstance(got, str) and got.startswith("UC_ERR")
                else:
                    ok = got == want
                fails += 0 if ok else 1
                mark = "ok  " if ok else "FAIL"
                gs = f"{got:#010x}" if isinstance(got, int) else got
                ws = f"{want:#010x}" if isinstance(want, int) else want
                print(f"[{vname}] {mark} {func}(base={base:#07x}): synth={gs} wasmtime={ws}")
    if fails:
        sys.exit(f"\n#681 differential: {fails} mismatches")
    print("\n#681 differential: all green (T4 ADDW static offsets, bounds honored)")


if __name__ == "__main__":
    main()
