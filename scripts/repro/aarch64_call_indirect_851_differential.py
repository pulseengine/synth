#!/usr/bin/env python3
# ci-status: wired
"""#851 lane L3 — aarch64 `call_indirect` execution differential vs wasmtime.

A64's `blr` is TOTAL: it branches wherever the register points. WASM §4.4.8 is
not — an indirect call TRAPS on an out-of-range index, on a null (uninitialized)
table slot, and on a signature mismatch. That gap is the #709 "more total than
WASM" silent-miscompile class, so the three traps are the POINT of this harness,
not a footnote: every one is asserted to fire exactly where wasmtime traps.

The dispatch it validates:

    cmp w_idx,#size / b.lo +2 / brk       out-of-range index
    adrp+add / add x16,x16,w_idx,uxtw#3   slot address (no base register)
    ldr w17,[x16] / cmp w17,#class        signature mismatch — and, since a
    b.eq +2 / brk                         null slot's id is 0 and every real
                                          class is >= 1, the null check too
    add x16,x16,#4 / blr x16              the slot's `b func_N` trampoline

What makes it non-vacuous:
  * the harness acts as the LINKER — it places `.text` itself and resolves the
    ADRP page / ADD lo12 / JUMP26 relocations, so a wrong table address or a
    wrong trampoline displacement calls the WRONG function and diverges;
  * BOTH directions are covered. Traps must fire (a missing guard = a wrong
    call), and the STRUCTURALLY-DUPLICATE type must NOT trap — a lowering that
    compared raw type indices would reject it, which is a trap where wasmtime
    calls (the mirror-image bug that "just always trap" would hide);
  * the expected column is taken from wasmtime FIRST, so the table cannot drift;
  * trap and value cases are counted separately and both must be non-zero.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_call_indirect_851_differential.py
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

WAT = Path(__file__).with_name("aarch64_call_indirect_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, DATA, STK, RET = 0x100000, 0x400000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
TRAP = "TRAP"

R_AARCH64_ADR_PREL_PG_HI21 = 275
R_AARCH64_ADD_ABS_LO12_NC = 277
R_AARCH64_CALL26 = 283
R_AARCH64_JUMP26 = 282

# fn -> ([arg widths], ret width or None for void).
SIGS = {
    "bin": ([32, 32, 32], 32),
    "bin_dup": ([32, 32, 32], 32),
    "bin_t1": ([32, 32, 32], 32),
    "un": ([32, 32], 32),
    "novoid": ([32], None),
    "chained": ([32], 32),
}

# (fn, args, why). The expected value/trap comes from wasmtime, never from here.
CASES = [
    # ---- in-range, correctly-typed dispatches (the value direction) ----
    ("bin", [10, 3, 0], "slot 0 = add -> 13"),
    ("bin", [10, 3, 1], "slot 1 = sub -> 7"),
    ("bin", [0, 1, 1], "sub underflow -> -1"),
    ("bin", [0x7FFFFFFF, 0xFFFFFFFF, 0], "add wraps"),
    ("un", [42, 2], "slot 2 = neg -> -42"),
    ("un", [0x80000000, 2], "neg(INT_MIN) wraps to itself"),
    ("chained", [0], "(7+5)*3 = 36 — the result feeds more arithmetic"),
    ("chained", [1], "(7-5)*3 = 6"),
    # ---- STRUCTURAL type equality: a DUPLICATE type must NOT trap ----
    # This is the direction "always trap" would silently pass; a lowering that
    # compared raw type indices would reject these, trapping where wasmtime calls.
    ("bin_dup", [10, 3, 0], "duplicate type at add -> 13, must NOT trap"),
    ("bin_dup", [10, 3, 1], "duplicate type at sub -> 7, must NOT trap"),
    # ---- TRAP: signature mismatch ----
    ("bin", [10, 3, 2], "slot 2 is unary, expected binary -> type mismatch"),
    ("bin_dup", [10, 3, 2], "same via the duplicate type"),
    ("un", [42, 0], "slot 0 is binary, expected unary -> type mismatch"),
    ("un", [42, 1], "slot 1 is binary, expected unary -> type mismatch"),
    ("novoid", [0], "no table entry has the void type -> mismatch"),
    ("novoid", [2], "ditto at another initialized slot"),
    # ---- TRAP: null (uninitialized) slot ----
    ("bin", [10, 3, 3], "slot 3 was never initialized -> null element"),
    ("un", [42, 3], "null slot via the unary dispatch"),
    ("novoid", [3], "null slot via the void dispatch"),
    ("chained", [3], "null slot reached through the chained entry"),
    # ---- TABLE 1: the per-table BASE OFFSET must be applied ----
    # $mul at region slot 4, NOT $add at region slot 0 — 30 vs 13.
    ("bin_t1", [10, 3, 0], "table 1 slot 0 = region slot 4 = mul -> 30"),
    ("bin_t1", [10, 3, 1], "table 1 slot 1 = region slot 5 = add -> 13"),
    ("bin_t1", [10, 3, 2], "past table 1's 2 entries -> out of range"),
    ("bin_t1", [10, 3, 0xFFFFFFFF], "unsigned OOB on table 1"),
    # ---- TRAP: out-of-range index ----
    # 4 and 5 are the LOAD-BEARING pair: they land on table 1's slots, which
    # are fully valid `$bin` trampolines with a MATCHING class id. Only the
    # bounds guard can trap here — drop it and these return 13 / 7 instead.
    ("bin", [10, 3, 4], "OOB onto table 1's valid, type-matching mul slot"),
    ("bin", [10, 3, 5], "OOB onto table 1's valid, type-matching add slot"),
    ("bin_dup", [10, 3, 4], "same, via the duplicate type"),
    ("chained", [4], "same, through the chained entry"),
    ("bin", [10, 3, 0x7FFFFFFF], "large positive index"),
    ("bin", [10, 3, 0xFFFFFFFF], "0xFFFFFFFF — UNSIGNED compare: a signed one "
                                 "would read it as -1 and fall through"),
    ("bin", [10, 3, 0x80000000], "sign bit set — same unsigned-compare trap"),
    ("un", [42, 4], "out of range via the unary dispatch"),
    ("un", [42, 6], "further past the end"),
    ("novoid", [9], "out of range via the void dispatch"),
    ("chained", [0xFFFFFFFF], "out of range through the chained entry"),
]


def wasmtime_run(fn, args, sig):
    """Fresh instance per call — the table is immutable here, so no state
    needs to carry over, and a trap leaves nothing behind."""
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, module, []).exports(store)[fn]
    widths, ret = sig
    conv = []
    for w, a in zip(widths, args):
        if w == 32:
            conv.append(struct.unpack("<i", struct.pack("<I", a & M32))[0])
        else:
            conv.append(struct.unpack("<q", struct.pack("<Q", a & M64))[0])
    try:
        r = f(store, *conv)
    except wasmtime.Trap:
        return TRAP
    if ret is None:
        return None
    return r & (M32 if ret == 32 else M64)


def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"aarch64 compile failed/skipped:\n{r.stdout}\n{r.stderr}")


def load_and_link(path):
    """Place `.text` at CODE (and `.data` at DATA if present) and resolve every
    relocation ourselves — this harness IS the linker."""
    f = ELFFile(open(path, "rb"))
    sections = list(f.iter_sections())
    text_sec = f.get_section_by_name(".text")
    data_sec = f.get_section_by_name(".data")
    text = bytearray(text_sec.data())
    data = bytearray(data_sec.data()) if data_sec is not None else bytearray()
    text_idx = sections.index(text_sec)
    data_idx = sections.index(data_sec) if data_sec is not None else -1

    sym_addr, by_name = {}, {}
    for i, sy in enumerate(f.get_section_by_name(".symtab").iter_symbols()):
        shndx = sy["st_shndx"]
        if shndx == text_idx:
            a = CODE + sy["st_value"]
        elif data_idx >= 0 and shndx == data_idx:
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
            target = sym_addr.get(r_sym)
            if target is None:
                sys.exit(f"relocation against an unplaced symbol (index {r_sym})")
            site = CODE + r_off
            word = struct.unpack_from("<I", text, r_off)[0]
            s = target + r["r_addend"]
            if r_type in (R_AARCH64_CALL26, R_AARCH64_JUMP26):
                word = (word & 0xFC000000) | (((s - site) // 4) & 0x03FFFFFF)
            elif r_type == R_AARCH64_ADR_PREL_PG_HI21:
                v = ((s >> 12) - (site >> 12)) & 0x1FFFFF
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


def emu_run(code, data, faddr, sig, args):
    widths, ret = sig
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(DATA, 0x10000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    if data:
        mu.mem_write(DATA, data)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    for r, (w, v) in zip(X_ARGS, zip(widths, args)):
        mu.reg_write(r, v & (M32 if w == 32 else M64))
    try:
        mu.emu_start(faddr, RET, count=200000)
    except UcError:
        return TRAP  # a guarded `brk #0` — a trap, not a value
    if ret is None:
        return None
    if ret == 32:
        return mu.reg_read(UC_ARM64_REG_W0) & M32
    return mu.reg_read(UC_ARM64_REG_X0) & M64


def main():
    out = "/tmp/aarch64_call_indirect_851.o"
    compile_aarch64(out)
    code, data, syms, applied = load_and_link(out)

    # Non-vacuity: the table must exist and be reached PC-relatively, and its
    # trampolines must have been relocated.
    if "__synth_func_table" not in syms:
        print("VACUOUS: no __synth_func_table symbol — no table was emitted")
        return 1
    for t, name in ((R_AARCH64_ADR_PREL_PG_HI21, "ADR_PREL_PG_HI21"),
                    (R_AARCH64_ADD_ABS_LO12_NC, "ADD_ABS_LO12_NC"),
                    (R_AARCH64_JUMP26, "JUMP26 (table trampolines)")):
        if applied.get(t, 0) == 0:
            print(f"VACUOUS: no {name} relocations applied")
            return 1

    fails = 0
    total = trap_cases = value_cases = 0
    seen = set()
    for fn, args, why in CASES:
        sig = SIGS[fn]
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing from the emitted object")
            fails += 1
            continue
        seen.add(fn)
        total += 1
        exp = wasmtime_run(fn, args, sig)
        if exp == TRAP:
            trap_cases += 1
        else:
            value_cases += 1
        got = emu_run(code, data, syms[fn], sig, args)
        if exp == TRAP or got == TRAP:
            ok = exp == got
        elif sig[1] is None:
            ok = got is None or got == exp
        else:
            ok = isinstance(got, int) and got == (exp & M32)
        if not ok:
            fails += 1
            e = exp if isinstance(exp, str) or exp is None else hex(exp)
            g = got if isinstance(got, str) or got is None else hex(got)
            print(f"BUG {fn}{tuple(hex(a) for a in args)} A64={g} wasmtime={e}  [{why}]")

    # Non-vacuity: both directions must have run, and every entry exercised.
    if trap_cases == 0:
        print("VACUOUS: no case trapped — the §4.4.8 guards were never exercised")
        fails += 1
    if value_cases == 0:
        print("VACUOUS: no case returned a value — only traps were exercised")
        fails += 1
    missing = set(SIGS) - seen
    if missing:
        print(f"VACUOUS: functions never exercised: {sorted(missing)}")
        fails += 1

    print(f"\n{total} checks ({trap_cases} trap, {value_cases} value) across "
          f"{len(seen)} exported functions; "
          f"{applied.get(R_AARCH64_JUMP26,0)} table trampolines relocated")
    print("RESULT:", "PASS — aarch64 call_indirect matches wasmtime, including "
          "the three §4.4.8 traps (out-of-range, null slot, signature mismatch) "
          "and the structurally-duplicate type that must NOT trap"
          if not fails else f"FAIL ({fails})")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
