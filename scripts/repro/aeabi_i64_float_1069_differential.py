#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 24000
"""#1069 (RQ-60-VFPPRESSURE increment 1) — the AEABI-routed i64<->f32
conversion family EXECUTION differential (cortex-m4f, Thumb-2, unicorn) vs
wasmtime.

Six ops under test, on the SINGLE-precision target where they previously
DECLINED outright ("requires a double-precision FPU target"):

  f32.convert_i64_{s,u}      -> bl __aeabi_l2f / __aeabi_ul2f (total)
  i64.trunc_f32_{s,u}        -> f32 domain guard (UDF) + bl __aeabi_f2lz/f2ulz
  i64.trunc_sat_f32_{s,u}    -> inline NaN/saturation select + bl (in-range only)

TRUST BOUNDARY, stated: on real hardware the `__aeabi_*` symbols come from the
embedder's runtime (libgcc / compiler-rt / kiln builtins) — a documented link
dependency of the route, not code synth emits. What THIS oracle verifies is
everything synth DOES emit: argument marshalling into the base-AAPCS core
registers, caller-saved preservation around the call, the f32 domain guard
(trap rows executed on both sides), the unsigned (-1,0)->+0 clamp, the inline
saturation/NaN selection, and result capture (f32 bits in R0 -> S-reg; i64 in
R0:R1). The builtins themselves are provided here as SPEC-EXACT stubs
(integer-arithmetic round-to-nearest-even for l2f/ul2f, truncation for
f2lz/f2ulz) computed in Python — and every stub ASSERTS its C-defined input
domain, so a guard hole that lets NaN/out-of-range reach the helper fails the
run even when the numeric answer happens to coincide.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aeabi_i64_float_1069_differential.py
"""

import math
import os
import random
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("aeabi_i64_float_1069.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
STUB_BASE = 0x0010_0000  # one `bx lr` per builtin, hooked below

CONVERTS = {"i64u_to_f32": False, "i64s_to_f32": True}  # fn -> signed
TRUNCS = {"f32_to_i64s": True, "f32_to_i64u": False}
SATS = {"f32_to_i64s_sat": True, "f32_to_i64u_sat": False}


# ---------------------------------------------------------------------------
# Spec-exact builtin stubs (pure integer arithmetic — no double rounding).
# ---------------------------------------------------------------------------
def u64_to_f32_bits(v):
    """Correctly-rounded (RNE) u64 -> f32, computed in exact integer math."""
    if v == 0:
        return 0
    nb = v.bit_length()
    e = nb - 1
    if nb <= 24:
        frac = v << (24 - nb)
    else:
        shift = nb - 24
        frac = v >> shift
        rem = v & ((1 << shift) - 1)
        half = 1 << (shift - 1)
        if rem > half or (rem == half and (frac & 1)):
            frac += 1
            if frac == 1 << 24:
                frac >>= 1
                e += 1
    return ((e + 127) << 23) | (frac & 0x7FFFFF)


def i64_to_f32_bits(v):
    if v >= 0:
        return u64_to_f32_bits(v)
    return 0x8000_0000 | u64_to_f32_bits(-v)


def f32_from_bits(bits):
    return struct.unpack("<f", struct.pack("<I", bits & M32))[0]


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def to_signed64(b):
    return b - (1 << 64) if b >> 63 else b


class Stubs:
    """The four AEABI helpers as hooked register transforms. Each asserts its
    C-defined input domain — reaching a stub with undefined input means a
    synth-emitted fence has a hole, and that is a FAILURE even if the
    numeric result would coincide."""

    def __init__(self):
        self.calls = 0

    def run(self, name, uc):
        self.calls += 1
        r0 = uc.reg_read(UC_ARM_REG_R0)
        r1 = uc.reg_read(UC_ARM_REG_R1)
        if name == "__aeabi_ul2f":
            uc.reg_write(UC_ARM_REG_R0, u64_to_f32_bits(r0 | (r1 << 32)))
        elif name == "__aeabi_l2f":
            uc.reg_write(UC_ARM_REG_R0, i64_to_f32_bits(to_signed64(r0 | (r1 << 32))))
        elif name == "__aeabi_f2ulz":
            v = f32_from_bits(r0)
            assert not math.isnan(v) and -1.0 < v < 2.0**64, (
                f"GUARD HOLE: __aeabi_f2ulz reached with undefined input {v!r}"
            )
            out = int(v) & M64  # int() truncates toward zero; (-1,0) -> 0
            uc.reg_write(UC_ARM_REG_R0, out & M32)
            uc.reg_write(UC_ARM_REG_R1, (out >> 32) & M32)
        elif name == "__aeabi_f2lz":
            v = f32_from_bits(r0)
            assert not math.isnan(v) and -(2.0**63) <= v < 2.0**63, (
                f"GUARD HOLE: __aeabi_f2lz reached with undefined input {v!r}"
            )
            out = int(v) & M64
            uc.reg_write(UC_ARM_REG_R0, out & M32)
            uc.reg_write(UC_ARM_REG_R1, (out >> 32) & M32)
        else:
            raise AssertionError(f"unexpected stub {name}")


# ---------------------------------------------------------------------------
def compile_or_die(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-t", "cortex-m4f",
         "--relocatable", "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    if r.returncode != 0:
        sys.exit(f"cortex-m4f --relocatable compile failed (the #1069 RED "
                 f"state): {r.stderr}")


def encode_thm_call(site, target):
    """Thumb-2 BL (T1) halfword pair for a branch from `site` to `target`."""
    off = target - (site + 4)
    assert -(1 << 24) <= off < (1 << 24) and off % 2 == 0
    s = (off >> 24) & 1
    i1 = (off >> 23) & 1
    i2 = (off >> 22) & 1
    imm10 = (off >> 12) & 0x3FF
    imm11 = (off >> 1) & 0x7FF
    j1 = (~(i1 ^ s)) & 1
    j2 = (~(i2 ^ s)) & 1
    hw1 = 0xF000 | (s << 10) | imm10
    hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
    return struct.pack("<HH", hw1, hw2)


def load(elf):
    """Return (.text bytes with builtin BLs re-targeted to stubs, base,
    {export: addr}, {stub_addr: builtin_name})."""
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = bytearray(text.data()), text["sh_addr"]
    syms = {}
    symtab = None
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            symtab = sec
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"]
    stub_addrs = {}
    next_stub = STUB_BASE
    rel = f.get_section_by_name(".rel.text")
    assert rel is not None, "no .rel.text — expected __aeabi_* call relocations"
    seen = set()
    for r in rel.iter_relocations():
        name = symtab.get_symbol(r["r_info_sym"]).name
        if not name.startswith("__aeabi_"):
            continue
        assert r["r_info_type"] == 10, f"{name}: expected R_ARM_THM_CALL"
        if name not in {a for a in stub_addrs.values()}:
            stub_addrs[next_stub] = name
            next_stub += 4
        addr = next(a for a, n in stub_addrs.items() if n == name)
        site = r["r_offset"]
        code[site - base:site - base + 4] = encode_thm_call(site, addr)
        seen.add(name)
    assert seen, "no __aeabi_* relocations found — the route did not fire"
    return bytes(code), base, syms, stub_addrs


# ---------------------------------------------------------------------------
def arm32_run(text, base, addr, stub_addrs, stubs, aty, arg_bits):
    """('ok', bits) / ('trap-udf', info) / ('fault', info) — result read from
    S0 (f32, AAPCS-VFP) or R0:R1 (i64)."""
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    uc.mem_map(0, 0x10000)  # .text at sh_addr (0) for an ET_REL
    uc.mem_write(base, text)
    uc.mem_map(STUB_BASE, 0x1000)
    for a in stub_addrs:
        uc.mem_write(a, b"\x70\x47")  # bx lr
    uc.mem_map(0x30000, 0x10000)  # stack
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)  # CPACR CP10/CP11
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)  # FPEXC.EN

    def on_stub(uc_, address, size, _user):
        if address in stub_addrs:
            stubs.run(stub_addrs[address], uc_)

    uc.hook_add(UC_HOOK_CODE, on_stub, begin=STUB_BASE, end=STUB_BASE + 0x1000)
    if aty == "i64":
        uc.reg_write(UC_ARM_REG_R0, arg_bits & M32)
        uc.reg_write(UC_ARM_REG_R1, (arg_bits >> 32) & M32)
    else:
        uc.reg_write(UC_ARM_REG_S0, arg_bits & M32)
    ret = 0x3F000
    uc.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        uc.emu_start(addr | 1, ret & ~1, count=4000)
    except UcError as e:
        pc = uc.reg_read(UC_ARM_REG_PC)
        kind = "fault"
        if base <= pc < base + len(text):
            hw = struct.unpack("<H", text[pc - base:pc - base + 2])[0]
            if hw & 0xFF00 == 0xDE00:  # Thumb UDF
                kind = "trap-udf"
        return (kind, f"{e} at pc={pc:#x}")
    if aty == "i64":  # convert: f32 result in S0
        return ("ok", uc.reg_read(UC_ARM_REG_S0) & M32)
    lo = uc.reg_read(UC_ARM_REG_R0) & M32
    hi = uc.reg_read(UC_ARM_REG_R1) & M32
    return ("ok", lo | (hi << 32))


# ---------------------------------------------------------------------------
def wasmtime_instance():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    return store, wasmtime.Instance(store, module, []).exports(store)


def check_convert(env, fn, pattern, fails, what):
    store, wexp, text, base, syms, stub_addrs, stubs = env
    try:
        want = f32_bits(wexp[fn](store, to_signed64(pattern)))
    except wasmtime.Trap:
        sys.exit(f"TABLE-BUG: wasmtime trapped on total {fn}({pattern:#x})")
    kind, got = arm32_run(text, base, syms[fn] & ~1, stub_addrs, stubs,
                          "i64", pattern)
    if kind != "ok":
        print(f"BUG [{what}] {fn}({pattern:#x}) -> {kind}: {got} — converts "
              f"are TOTAL (wasmtime bits {want:#x})")
        return fails + 1
    if got != want:
        print(f"BUG [{what}] {fn}({pattern:#x}) = {got:#x} != wasmtime {want:#x}")
        return fails + 1
    return fails


def check_trunc(env, fn, bits, trapping, fails, what):
    store, wexp, text, base, syms, stub_addrs, stubs = env
    v = f32_from_bits(bits)
    try:
        want = ("ok", int(wexp[fn](store, v)) & M64)
    except wasmtime.Trap:
        want = ("trap", None)
    kind, got = arm32_run(text, base, syms[fn] & ~1, stub_addrs, stubs,
                          "f32", bits)
    if want[0] == "trap":
        assert trapping, f"TABLE-BUG: wasmtime trapped on trunc_sat {fn}({v!r})"
        if kind != "trap-udf":
            print(f"BUG [{what}] {fn}({v!r}): wasmtime TRAPS but ARM "
                  f"{'returned ' + hex(got) if kind == 'ok' else kind} — the "
                  f"#709-class silent-miscompile (missing domain guard)")
            return fails + 1
        return fails
    if kind != "ok":
        print(f"BUG [{what}] {fn}({v!r}) -> {kind}: {got} — wasmtime returns "
              f"{want[1]:#x} (guard over-traps)")
        return fails + 1
    if got != want[1]:
        print(f"BUG [{what}] {fn}({v!r}) = {got:#x} != wasmtime {want[1]:#x}")
        return fails + 1
    return fails


# ---------------------------------------------------------------------------
def i64_boundary_patterns():
    pats = set()
    for v in [0, 1, 2, 0xFF, 0xFFFF, 0xFFFFFFFF, 1 << 32, (1 << 32) + 1,
              (1 << 53) - 1, 1 << 53, (1 << 53) + 1, (1 << 63) - 1, 1 << 63,
              (1 << 63) + 1, M64, M64 - 1,
              0x8000_0080_0000_0001,  # the #869 double-rounding killer
              0x8000_0080_0000_0000, 0xFFFF_FF7F_FFFF_FFFF,
              0x0000_0000_FFFF_FF7F, 0x7FFF_FFC0_0000_0000]:
        pats.add(v & M64)
    for k in range(0, 64, 3):
        pats.update({(1 << k) & M64, ((1 << k) - 1) & M64, ((1 << k) + 1) & M64})
    return sorted(pats)


def f32_boundary_bits():
    vals = [0.0, -0.0, 0.5, -0.5, 1.0, -1.0, 1.5, -1.5, -0.9999999,
            8388607.5, 2.0**31, 2.0**31 - 128, 2.0**32, 2.0**52,
            9223371487098961920.0,   # largest f32 < 2^63
            2.0**63, -(2.0**63),     # trap-s boundary / exact min
            -9223373136366403584.0,  # next f32 below -2^63 (traps signed)
            18446742974197923840.0,  # largest f32 < 2^64
            2.0**64, -(2.0**64), float("inf"), -float("inf")]
    bits = {f32_bits(v) for v in vals}
    bits.update({0x7FC00000, 0xFFC00000, 0x7F800001, 0x7FFFFFFF})  # NaNs
    return sorted(bits)


def _rand_u64(rng):
    r = rng.random()
    if r < 0.40:
        return rng.getrandbits(64)
    if r < 0.70:  # tie-prone: short mantissa shifted high
        return (rng.getrandbits(rng.randint(1, 25)) << rng.randint(0, 39)) & M64
    if r < 0.90:
        return rng.getrandbits(rng.randint(1, 16))
    return (1 << rng.randint(0, 63)) + rng.randint(-2, 2) & M64


def _rand_f32_bits(rng):
    r = rng.random()
    if r < 0.5:
        return rng.getrandbits(32)
    # exponent band around the interesting 2^62..2^65 / small-integer range
    sign = rng.getrandbits(1) << 31
    exp = rng.randint(120, 191) << 23
    return sign | exp | rng.getrandbits(23)


# ---------------------------------------------------------------------------
def main():
    elf = "/tmp/aeabi_1069_m4f.o"
    compile_or_die(elf)
    text, base, syms, stub_addrs = load(elf)
    for fn in list(CONVERTS) + list(TRUNCS) + list(SATS):
        assert fn in syms, f"{fn} missing from symtab — the #1069 skip class"
    stubs = Stubs()
    store, wexp = wasmtime_instance()
    env = (store, wexp, text, base, syms, stub_addrs, stubs)
    rng = random.Random(1069)
    fails = 0
    checks = 0

    for fn in CONVERTS:
        for p in i64_boundary_patterns():
            fails = check_convert(env, fn, p, fails, "boundary")
            checks += 1
        for _ in range(4000):
            fails = check_convert(env, fn, _rand_u64(rng), fails, "fuzz")
            checks += 1

    for group, trapping in ((TRUNCS, True), (SATS, False)):
        for fn in group:
            for b in f32_boundary_bits():
                fails = check_trunc(env, fn, b, trapping, fails, "boundary")
                checks += 1
            for _ in range(4000):
                fails = check_trunc(env, fn, _rand_f32_bits(rng), trapping, fails, "fuzz")
                checks += 1

    print(f"{checks} checks ({stubs.calls} stubbed builtin calls), "
          f"{fails} failures")
    if fails:
        sys.exit(1)
    print("PASS")


if __name__ == "__main__":
    main()
