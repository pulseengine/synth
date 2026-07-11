#!/usr/bin/env python3
"""#708/#709 — EXECUTION-validate the phase-1b thumb-2 f32 increment.

Two capabilities land on the v0.39.0 hard-float path:

  #709 (SOUNDNESS): `i32.trunc_f32_s/u` were lowered to a BARE saturating VCVT
    (NaN->0, out-of-range->saturated) where WASM Core §4.3.3 mandates a TRAP.
    The fix emits a domain guard (VCMP against the exact f32-representable
    bounds + VMRS + ordered conditional branch, div-by-zero-style `B<c> +0 / UDF`)
    BEFORE the VCVT. This harness runs the exact #709 trap table on Cortex-M4F
    under unicorn and asserts every NaN/Inf/out-of-range input STOPS AT A UDF
    (like the #374/#642 trap oracles), while in-range inputs stay bit-exact vs
    wasmtime.

  #708: `f32.load` (lowered as the proven i32.load address sequence + a VMOV
    bitcast into an S-register) and the `i32.reinterpret_f32` / `f32.reinterpret_i32`
    bit-casts (pure VMOV). Asserted bit-exact vs wasmtime.

RED on origin/main: `trunc` traps are MISSED (returns a saturated value, not a
UDF) and `f32.load`/reinterpret REJECT at compile (capability gap) -> nonzero.
GREEN after this PR -> exit 0.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python scripts/repro/f32_mem_trunc_708_709_differential.py
"""
import math
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("f32_mem_trunc_708_709.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Linear-memory base the self-contained cortex-m image loads into R11/fp at
# reset (cortex_m.rs: R11 = 0x2000_0000). The harness runs functions directly,
# so we place a mapped window there and set R11 to it.
MEMBASE = 0x20000000


def compile_elf(out, target):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", target, "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    return r.returncode == 0, (r.stderr + r.stdout)


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":  # #489: synth emits an unnamed symtab
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def bits_f32(b):
    return struct.unpack("<f", struct.pack("<I", b & 0xFFFFFFFF))[0]


def new_uc(text, text_base):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    map_base = text_base & ~0xFFF
    size = ((len(text) + (text_base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(text_base, text)
    uc.mem_map(0x30000, 0x10000)  # stack
    uc.mem_map(MEMBASE, 0x10000)  # linear memory window (R11/fp base)
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    uc.reg_write(UC_ARM_REG_R11, MEMBASE)
    # Enable the FPU (M4F FPU is off at reset): CPACR CP10/CP11 + FPEXC.EN.
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    return uc


def run(text, base, addr, *, s0=None, r0=None):
    """Execute one function. Returns ('ok', uc) or ('trap-udf', pc) or ('fault', msg)."""
    uc = new_uc(text, base)
    if s0 is not None:
        uc.reg_write(UC_ARM_REG_S0, s0)
    if r0 is not None:
        uc.reg_write(UC_ARM_REG_R0, r0 & 0xFFFFFFFF)
    ret = 0x38000
    from unicorn.arm_const import UC_ARM_REG_LR
    uc.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        uc.emu_start(addr | 1, ret & ~1, count=200)
    except UcError as e:
        pc = uc.reg_read(UC_ARM_REG_PC)
        if base <= pc < base + len(text):
            hw = struct.unpack("<H", text[pc - base : pc - base + 2])[0]
            if hw & 0xFF00 == 0xDE00:  # Thumb UDF #imm
                return ("trap-udf", pc)
        return ("fault", f"{e} at pc={pc:#x} (NOT a udf trap)")
    return ("ok", uc)


def wasm_instance():
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    return store, inst


# ---- #709 trap tables (the EXACT issue table) -----------------------------
NAN = float("nan")
INF = float("inf")
TRUNC_S = [
    (2.5, "ok"), (NAN, "trap"), (INF, "trap"), (-INF, "trap"),
    (3e9, "trap"), (-3e9, "trap"), (2147483648.0, "trap"),  # 2^31 exactly
    # extra in-range bit-exact anchors:
    (0.0, "ok"), (-2.5, "ok"), (123.75, "ok"), (-123.75, "ok"),
    (2147483000.0, "ok"), (-2147483648.0, "ok"),  # -2^31 exactly is IN range
]
TRUNC_U = [
    (2.5, "ok"), (NAN, "trap"), (-1.0, "trap"), (INF, "trap"), (5e9, "trap"),
    # extra in-range bit-exact anchors:
    (0.0, "ok"), (0.5, "ok"), (123.75, "ok"), (4000000000.0, "ok"),
    (4294967000.0, "ok"),
]


def main():
    elf = "/tmp/f32_mem_trunc_708_709.elf"

    # Honest-reject on a no-FPU target (m3) must still hold.
    ok_m3, _ = compile_elf("/tmp/f32_mt_m3.elf", "cortex-m3")
    if ok_m3:
        sys.exit("FAIL: f32 must be REJECTED on cortex-m3 (no FPU), but compiled")

    ok, log = compile_elf(elf, "cortex-m4f")
    if not ok:
        print("RED: `synth compile -t cortex-m4f` REJECTED the f32 fixture.")
        print(log.strip()[:600])
        sys.exit(1)

    text, base, syms = load(elf)
    store, inst = wasm_instance()
    exp = inst.exports(store)
    fails = 0
    checked = 0

    def wasm_call_or_trap(fn, *args):
        try:
            return exp[fn](store, *args)
        except wasmtime.Trap:
            return "trap"

    # ---- #709 trunc trap tables ----
    for fn, table in (("trunc_s", TRUNC_S), ("trunc_u", TRUNC_U)):
        for x, want_kind in table:
            kind, payload = run(text, base, syms[fn], s0=f32_bits(x))
            wv = wasm_call_or_trap(fn, x)
            checked += 1
            xr = "NaN" if math.isnan(x) else repr(x)
            if want_kind == "trap":
                if wv != "trap":
                    sys.exit(f"BUG in oracle: wasmtime did not trap on {fn}({xr})")
                if kind == "trap-udf":
                    print(f"[#709] {fn}({xr}) -> UDF trap @ {payload:#x} "
                          f"(wasmtime: trap) OK")
                else:
                    fails += 1
                    print(f"[#709] {fn}({xr}) -> {kind}:{payload} "
                          f"(wasmtime: trap) MISMATCH — MISSED TRAP")
            else:
                want = wv & 0xFFFFFFFF
                if kind != "ok":
                    fails += 1
                    print(f"[#709] {fn}({xr}) -> {kind}:{payload} "
                          f"(wasmtime: {want}) MISMATCH — spurious trap")
                    continue
                got = payload.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
                if got != want:
                    fails += 1
                    print(f"[#709] {fn}({xr}) -> {got} != wasmtime {want} MISMATCH")
                else:
                    print(f"[#709] {fn}({xr}) = {got} (wasmtime: {want}) OK")

    # ---- #708 f32.load: write a known word, load it, compare bits ----
    mem = exp["mem"]
    LOAD_CASES = [(0, 0x3FC00000),   # 1.5
                  (16, 0xC0100000),  # -2.25
                  (64, 0x7F800000),  # +Inf bit pattern (load is a pure bitcopy)
                  (128, 0x00000001)]  # subnormal-ish tiny
    for addr, word in LOAD_CASES:
        # seed wasmtime + unicorn memories identically
        mem.write(store, struct.pack("<I", word), addr)
        uc = new_uc(text, base)
        uc.mem_write(MEMBASE + addr, struct.pack("<I", word))
        from unicorn.arm_const import UC_ARM_REG_LR
        uc.reg_write(UC_ARM_REG_R0, addr)
        uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
        uc.emu_start(syms["load"] | 1, 0x38000, count=200)
        got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
        want = f32_bits(exp["load"](store, addr))
        checked += 1
        if got != want or got != word:
            fails += 1
            print(f"[#708] load[{addr}] -> 0x{got:08x} != want 0x{want:08x} "
                  f"(mem 0x{word:08x}) MISMATCH")
        else:
            print(f"[#708] load[{addr}] = 0x{got:08x} (wasmtime bit-exact) OK")

    # ---- #708 reinterprets + round-trip ----
    REINT = [0x3FC00000, 0xC0100000, 0x7FC00000, 0x80000000, 0x00000000,
             0xFFFFFFFF, 0x12345678]
    for word in REINT:
        # i32.reinterpret_f32(x): S0 bits -> R0 (== bits)
        kind, uc = run(text, base, syms["r2i"], s0=word)
        got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF if kind == "ok" else None
        want = exp["r2i"](store, bits_f32(word)) & 0xFFFFFFFF
        checked += 1
        if got != want or got != word:
            fails += 1
            print(f"[#708] r2i(0x{word:08x}) -> {got} != want 0x{want:08x} MISMATCH")
        else:
            print(f"[#708] r2i(0x{word:08x}) = 0x{got:08x} OK")

        # f32.reinterpret_i32(i): R0 -> S0 (== bits)
        kind, uc = run(text, base, syms["i2r"], r0=word)
        got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF if kind == "ok" else None
        want = f32_bits(exp["i2r"](store, word))
        checked += 1
        if got != want or got != word:
            fails += 1
            print(f"[#708] i2r(0x{word:08x}) -> {got} != want 0x{want:08x} MISMATCH")
        else:
            print(f"[#708] i2r(0x{word:08x}) = 0x{got:08x} OK")

        # round-trip rt(i) == i
        kind, uc = run(text, base, syms["rt"], r0=word)
        got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF if kind == "ok" else None
        checked += 1
        if got != word:
            fails += 1
            print(f"[#708] rt(0x{word:08x}) -> {got} != 0x{word:08x} MISMATCH")
        else:
            print(f"[#708] rt(0x{word:08x}) = 0x{got:08x} OK")

    if fails:
        sys.exit(f"\nFAIL: {fails}/{checked} f32 #708/#709 results diverged")
    print(f"\nGREEN: {checked}/{checked} f32 #708/#709 results correct "
          f"(trap table + load + reinterpret; m3 honest-reject confirmed).")


if __name__ == "__main__":
    main()
