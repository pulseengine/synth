#!/usr/bin/env python3
"""#851 lane L3 — aarch64 WASM GLOBALS execution differential vs wasmtime.

synth emits the globals region ITSELF: a `.data` section carrying each global's
decoded constant initializer, named `__synth_globals`, reached from code by an
`adrp` + `add :lo12:` pair. There is NO globals base register and therefore NO
precondition — unlike `x28` (the linear-memory base), which the embedder
supplies. This harness proves the emitted region and the emitted addressing
agree with wasmtime, including that STORES PERSIST across calls.

What makes it non-vacuous:
  * the harness acts as the LINKER — it places `.text` and `.data` at distinct
    addresses and resolves the ADRP page / ADD lo12 relocations itself, so a
    wrong page delta or a wrong lo12 lands on the wrong bytes and the values
    diverge (an unrelocated `adrp #0` would address the code page);
  * calls run IN SEQUENCE against ONE region, so a `global.set` that silently
    dropped (or wrote the wrong slot) shows up in the next `global.get`;
  * the INITIAL values are read back before anything is written, so a region
    that shipped zeros instead of the decoded initializers fails;
  * i32 and i64 globals are interleaved, so a wrong slot stride (the uniform
    8-byte layout vs a dense one) shifts every later global and fails;
  * the run asserts a non-zero check count and that every exported function was
    exercised.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_globals_851_differential.py
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
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
    UC_ARM64_REG_X2,
)

WAT = Path(__file__).with_name("aarch64_globals_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Deliberately on DIFFERENT 4 KiB pages, and far enough apart that the ADRP
# page delta is non-zero — a harness that placed them on one page would not
# exercise the relocation at all.
CODE, DATA, STK, RET = 0x100000, 0x400000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
TRAP = "TRAP"

R_AARCH64_ADR_PREL_PG_HI21 = 275
R_AARCH64_ADD_ABS_LO12_NC = 277
R_AARCH64_CALL26 = 283
R_AARCH64_JUMP26 = 282

# fn -> ([arg widths], ret width). None ret = void.
SIGS = {
    "get_i32": ([], 32),
    "get_i64": ([], 64),
    "get_second_i32": ([], 32),
    "bump": ([32], 32),
    "set_i64": ([64], 64),
    "sum_all": ([], 64),
}

# Executed IN ORDER against ONE region (both oracles), so persistence is tested.
CASES = [
    # --- initial values, read BEFORE anything is written ---
    ("get_i32", []),          # 41
    ("get_i64", []),          # 1234567890123
    ("get_second_i32", []),   # -7
    ("sum_all", []),          # 41 + 1234567890123 + (-7)
    # --- mutation persists ---
    ("bump", [1]),            # 42
    ("bump", [1]),            # 43
    ("get_i32", []),          # 43  (the store persisted)
    ("bump", [0xFFFFFFFF]),   # 42  (add -1)
    ("bump", [1000]),         # 1042
    # --- 64-bit slot: both words must reach the region ---
    ("set_i64", [0x7FFF_FFFF_FFFF_FFFF]),
    ("get_i64", []),
    ("set_i64", [0xFFFF_FFFF_FFFF_FFFF]),   # -1: upper word must not be lost
    ("get_i64", []),
    ("set_i64", [0x0000_0001_0000_0000]),   # only the UPPER word is set
    ("get_i64", []),
    # --- the other i32 global is unaffected by all of the above ---
    ("get_second_i32", []),   # still -7
    ("sum_all", []),
]


def wasmtime_session():
    """One instance, so globals persist across the case sequence."""
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = inst.exports(store)

    def call(fn, args, sig):
        widths, _ret = sig
        conv = []
        for w, a in zip(widths, args):
            if w == 32:
                conv.append(struct.unpack("<i", struct.pack("<I", a & M32))[0])
            else:
                conv.append(struct.unpack("<q", struct.pack("<Q", a & M64))[0])
        try:
            r = exports[fn](store, *conv)
        except wasmtime.Trap:
            return TRAP
        if r is None:
            return None
        return r & (M32 if sig[1] == 32 else M64)

    return call


def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"aarch64 compile failed/skipped:\n{r.stdout}\n{r.stderr}")


def load_and_link(path):
    """Read the object, place .text at CODE and .data at DATA, and resolve
    every relocation ourselves (this harness IS the linker)."""
    f = ELFFile(open(path, "rb"))
    text_sec = f.get_section_by_name(".text")
    data_sec = f.get_section_by_name(".data")
    if text_sec is None:
        sys.exit("emitted object has no .text")
    if data_sec is None:
        sys.exit("emitted object has NO .data section — the globals region was "
                 "not emitted (the whole point of this lane)")
    text = bytearray(text_sec.data())
    data = bytearray(data_sec.data())
    text_idx = list(f.iter_sections()).index(text_sec)
    data_idx = list(f.iter_sections()).index(data_sec)

    # symbol index -> absolute address; also name -> address.
    sym_addr, by_name = {}, {}
    symtab = f.get_section_by_name(".symtab")
    for i, sy in enumerate(symtab.iter_symbols()):
        shndx = sy["st_shndx"]
        if shndx == text_idx:
            a = CODE + sy["st_value"]
        elif shndx == data_idx:
            a = DATA + sy["st_value"]
        else:
            continue
        sym_addr[i] = a
        if sy.name:
            by_name.setdefault(sy.name, a)

    applied = {}
    rela = f.get_section_by_name(".rela.text")
    if rela is not None:
        for r in rela.iter_relocations():
            r_off = r["r_offset"]
            r_type = r["r_info_type"]
            r_sym = r["r_info"] >> 32
            addend = r["r_addend"]
            target = sym_addr.get(r_sym)
            if target is None:
                sys.exit(f"relocation against an unplaced symbol (index {r_sym})")
            site = CODE + r_off
            word = struct.unpack_from("<I", text, r_off)[0]
            s = target + addend
            if r_type in (R_AARCH64_CALL26, R_AARCH64_JUMP26):
                disp = (s - site) // 4
                word = (word & 0xFC000000) | (disp & 0x03FFFFFF)
            elif r_type == R_AARCH64_ADR_PREL_PG_HI21:
                delta = (s >> 12) - (site >> 12)
                v = delta & 0x1FFFFF
                word &= ~((0x3 << 29) | (0x7FFFF << 5))
                word |= (v & 0x3) << 29
                word |= ((v >> 2) & 0x7FFFF) << 5
            elif r_type == R_AARCH64_ADD_ABS_LO12_NC:
                word = (word & ~(0xFFF << 10)) | ((s & 0xFFF) << 10)
            else:
                sys.exit(f"unexpected relocation type {r_type}")
            struct.pack_into("<I", text, r_off, word)
            applied[r_type] = applied.get(r_type, 0) + 1
    return bytes(text), bytes(data), by_name, applied


class Emu:
    """One long-lived emulator so `.data` writes persist across calls."""

    def __init__(self, code, data):
        self.mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        self.mu.mem_map(CODE, 0x20000)
        self.mu.mem_map(DATA, 0x10000)
        self.mu.mem_map(STK - 0x10000, 0x20000)
        self.mu.mem_map(RET & ~0xFFF, 0x1000)
        self.mu.mem_write(CODE, code)
        self.mu.mem_write(DATA, data)

    def run(self, faddr, sig, args):
        widths, ret = sig
        self.mu.reg_write(UC_ARM64_REG_SP, STK)
        self.mu.reg_write(UC_ARM64_REG_LR, RET)
        for r, (w, v) in zip(X_ARGS, zip(widths, args)):
            self.mu.reg_write(r, v & (M32 if w == 32 else M64))
        try:
            self.mu.emu_start(faddr, RET, count=200000)
        except UcError:
            return TRAP
        if ret == 32:
            return self.mu.reg_read(UC_ARM64_REG_W0) & M32
        return self.mu.reg_read(UC_ARM64_REG_X0) & M64


def main():
    out = "/tmp/aarch64_globals_851.o"
    compile_aarch64(out)
    code, data, syms, applied = load_and_link(out)

    # Non-vacuity: the ADRP/ADD pair must actually have been relocated, or the
    # run would prove nothing about the addressing this lane added.
    for t, name in ((R_AARCH64_ADR_PREL_PG_HI21, "ADR_PREL_PG_HI21"),
                    (R_AARCH64_ADD_ABS_LO12_NC, "ADD_ABS_LO12_NC")):
        if applied.get(t, 0) == 0:
            print(f"VACUOUS: no {name} relocations were applied — the globals "
                  f"region is not being addressed PC-relatively")
            return 1
    if "__synth_globals" not in syms:
        print("VACUOUS: no __synth_globals symbol in the object")
        return 1

    emu = Emu(code, data)
    wt_call = wasmtime_session()

    fails, total = 0, 0
    seen = set()
    for fn, args in CASES:
        sig = SIGS[fn]
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing from the emitted object")
            fails += 1
            continue
        seen.add(fn)
        total += 1
        exp = wt_call(fn, args, sig)
        got = emu.run(syms[fn], sig, args)
        ok = (exp == got) if (exp == TRAP or got == TRAP) else \
            (isinstance(got, int) and got == (exp & (M32 if sig[1] == 32 else M64)))
        if not ok:
            fails += 1
            e = exp if isinstance(exp, str) else hex(exp)
            g = got if isinstance(got, str) else hex(got)
            print(f"BUG {fn}{tuple(hex(a) for a in args)} A64={g} wasmtime={e}")

    missing = set(SIGS) - seen
    if missing:
        print(f"VACUOUS: functions never exercised: {sorted(missing)}")
        fails += 1
    if total == 0:
        print("VACUOUS: zero checks ran")
        fails += 1

    print(f"\n{total} checks across {len(seen)} exported functions "
          f"({applied.get(R_AARCH64_ADR_PREL_PG_HI21,0)} ADRP + "
          f"{applied.get(R_AARCH64_ADD_ABS_LO12_NC,0)} ADD lo12 relocations applied)")
    print("RESULT:", "PASS — aarch64 global.get/global.set match wasmtime "
          "(initial values, i32+i64 slots, stores persisting across calls)"
          if not fails else f"FAIL ({fails})")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
