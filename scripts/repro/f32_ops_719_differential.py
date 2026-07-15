#!/usr/bin/env python3
"""#719 — EXECUTION-validate the phase-1b thumb-2 f32 residual increment.

After #708 (f32.load + reinterpret) landed, falcon's float functions skip on the
NEXT unsupported f32 op. #719 lands the residual:

  * f32.store            — VFP-store twin of f32.load (VMOV Rn,Sn + i32.store path)
  * f32.abs / f32.neg    — VABS.F32 / VNEG.F32
  * f32.copysign         — sign-bit splice (bit-exact ±0 / NaN-sign / ±inf)
  * f32 local.set/tee     — VFP home write-back
  * mixed f32/int params  — AAPCS-VFP independent core (R0..) / VFP (S0..) pools

Each op is differentiated on Cortex-M4F under unicorn vs wasmtime, BIT-EXACT (the
sign edges compare the 32-bit pattern, not the float value — -0.0 == +0.0 by
value but differs in bits). RED on origin/main: every op REJECTS at compile
(capability gap) -> nonzero. GREEN after #719 -> exit 0.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python scripts/repro/f32_ops_719_differential.py
"""
import math
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_S0,
    UC_ARM_REG_S1,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("f32_ops_719.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
MEMBASE = 0x20000000  # R11/fp linear-memory base at reset (cortex_m.rs)


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


def is_nan32(bits):
    b = bits & 0xFFFFFFFF
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


def f32_bits_eq(got, want):
    """WASM leaves the sign+payload of a NaN result NON-DETERMINISTIC (Core
    4.3.3 NaN propagation) -- a bit-exact compare of a NaN is over-specified
    and diverges by wasmtime version. NaN==NaN regardless of bits; every
    non-NaN result stays bit-exact (mirrors f32_vfp_619_differential.py)."""
    if is_nan32(got) and is_nan32(want):
        return True
    return (got & 0xFFFFFFFF) == (want & 0xFFFFFFFF)


def bits_f32(b):
    return struct.unpack("<f", struct.pack("<I", b & 0xFFFFFFFF))[0]


def new_uc(text, text_base):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    map_base = text_base & ~0xFFF
    size = ((len(text) + (text_base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(text_base, text)
    uc.mem_map(0x30000, 0x10000)  # stack
    uc.mem_map(MEMBASE, 0x10000)  # linear-memory window (R11/fp base)
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    uc.reg_write(UC_ARM_REG_R11, MEMBASE)
    # Enable the FPU (M4F FPU is off at reset): CPACR CP10/CP11 + FPEXC.EN.
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    return uc


def run(text, base, addr, *, r0=None, r1=None, s0=None, s1=None):
    """Execute one function; return the unicorn context (post-return)."""
    uc = new_uc(text, base)
    if r0 is not None:
        uc.reg_write(UC_ARM_REG_R0, r0 & 0xFFFFFFFF)
    if r1 is not None:
        uc.reg_write(UC_ARM_REG_R1, r1 & 0xFFFFFFFF)
    if s0 is not None:
        uc.reg_write(UC_ARM_REG_S0, s0 & 0xFFFFFFFF)
    if s1 is not None:
        uc.reg_write(UC_ARM_REG_S1, s1 & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=200)
    return uc


def wasm_instance():
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    return store, inst


# Bit patterns exercising the sign edges + normal magnitudes.
EDGE_BITS = [
    0x00000000,  # +0.0
    0x80000000,  # -0.0
    0x3FC00000,  # 1.5
    0xBFC00000,  # -1.5
    0x7F800000,  # +inf
    0xFF800000,  # -inf
    0x7FC00000,  # +NaN (quiet)
    0xFFC00000,  # -NaN (sign set)
    0x00000001,  # +subnormal tiny
    0x80000001,  # -subnormal tiny
    0x42F60000,  # 123.0
    0xC2F60000,  # -123.0
    0x7F7FFFFF,  # +FLT_MAX
]


def main():
    elf = "/tmp/f32_ops_719.elf"

    # Honest-reject on a no-FPU target (m3): every f32 fn must be REJECTED, so
    # the whole compile fails (no functions emitted).
    ok_m3, _ = compile_elf("/tmp/f32_ops_719_m3.elf", "cortex-m3")
    if ok_m3:
        sys.exit("FAIL: f32 fixture must be REJECTED on cortex-m3 (no FPU)")

    ok, log = compile_elf(elf, "cortex-m4f")
    if not ok:
        print("RED: `synth compile -t cortex-m4f` REJECTED the #719 f32 fixture.")
        print(log.strip()[:900])
        sys.exit(1)

    text, base, syms = load(elf)
    store, inst = wasm_instance()
    exp = inst.exports(store)
    mem = exp["mem"]
    fails = 0
    checked = 0

    def need(name):
        if name not in syms:
            nonlocal_fail(f"symbol '{name}' MISSING — function was skipped, not lowered")
            return False
        return True

    def nonlocal_fail(msg):
        nonlocal fails
        fails += 1
        print("  MISMATCH " + msg)

    # ---- abs / neg / lset / ltee: bits in R0 -> bits in R0 ----
    for fn, wname in (("abs", "abs"), ("neg", "neg"), ("lset", "lset"),
                      ("ltee", "ltee")):
        if not need(fn):
            continue
        for b in EDGE_BITS:
            uc = run(text, base, syms[fn], r0=b)
            got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            want = exp[wname](store, b) & 0xFFFFFFFF
            checked += 1
            if got != want:
                nonlocal_fail(f"{fn}(0x{b:08x}) -> 0x{got:08x} != wasmtime 0x{want:08x}")
            else:
                print(f"[{fn}] 0x{b:08x} -> 0x{got:08x} (bit-exact) OK")

    # ---- copysign(a, b): a=R0 (magnitude), b=R1 (sign) -> R0 ----
    if need("copysign"):
        for a in EDGE_BITS:
            for b in (0x00000000, 0x80000000, 0x7FC00000, 0xFFC00000,
                      0x3F800000, 0xBF800000):
                uc = run(text, base, syms["copysign"], r0=a, r1=b)
                got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
                want = exp["copysign"](store, a, b) & 0xFFFFFFFF
                checked += 1
                if got != want:
                    nonlocal_fail(
                        f"copysign(0x{a:08x},0x{b:08x}) -> 0x{got:08x} "
                        f"!= wasmtime 0x{want:08x}")
        print(f"[copysign] {len(EDGE_BITS)*6} sign-splice cases checked")

    # ---- f32.store(addr, bits): store to mem[addr], read back ----
    if need("store"):
        for i, b in enumerate(EDGE_BITS):
            addr = 16 * i
            uc = new_uc(text, base)
            uc.reg_write(UC_ARM_REG_R0, addr)
            uc.reg_write(UC_ARM_REG_R1, b)
            uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
            uc.emu_start(syms["store"] | 1, 0x38000, count=200)
            got = struct.unpack("<I", uc.mem_read(MEMBASE + addr, 4))[0]
            # wasmtime: store then read the same word back.
            exp["store"](store, addr, b)
            want = struct.unpack("<I", mem.read(store, addr, addr + 4))[0]
            checked += 1
            if got != want or got != b:
                nonlocal_fail(f"store[{addr}]=0x{b:08x} -> mem 0x{got:08x} "
                              f"!= wasmtime 0x{want:08x}")
            else:
                print(f"[store] mem[{addr}] = 0x{got:08x} (bit-exact) OK")

    # ---- mixed f32/int params (AAPCS-VFP independent pools) ----
    # mix_if(i32 a, f32 x) -> bits(a + reinterpret(x)); a in R0, x in S0.
    if need("mix_if"):
        for a, xb in ((7, 0x3FC00000), (0x1000, 0x7F800000), (0xFFFFFFFF, 0x80000000)):
            uc = run(text, base, syms["mix_if"], r0=a, r1=0xDEADBEEF, s0=xb)
            got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            want = exp["mix_if"](store, a, bits_f32(xb)) & 0xFFFFFFFF
            checked += 1
            if got != want:
                nonlocal_fail(f"mix_if(0x{a:08x},0x{xb:08x}) -> 0x{got:08x} "
                              f"!= wasmtime 0x{want:08x}")
            else:
                print(f"[mix_if] (0x{a:08x},0x{xb:08x}) -> 0x{got:08x} OK")

    # mix_fi(f32 x, i32 i) -> bits(reinterpret(x) + i); x in S0, i in R0.
    # R1 poisoned: the old bug read the i32 param from R1 (pool-collision).
    if need("mix_fi"):
        for xb, i in ((0x3FC00000, 9), (0x7F800000, 0x2000), (0x80000000, 0xFFFFFFFF)):
            uc = run(text, base, syms["mix_fi"], r0=i, r1=0xBADC0DE, s0=xb)
            got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            want = exp["mix_fi"](store, bits_f32(xb), i) & 0xFFFFFFFF
            checked += 1
            if got != want:
                nonlocal_fail(f"mix_fi(0x{xb:08x},0x{i:08x}) -> 0x{got:08x} "
                              f"!= wasmtime 0x{want:08x}")
            else:
                print(f"[mix_fi] (0x{xb:08x},0x{i:08x}) -> 0x{got:08x} OK")

    # mix_store(i32 addr, f32 val): addr in R0, val in S0.
    if need("mix_store"):
        for i, b in enumerate((0x3FC00000, 0xFF800000, 0x7FC00000, 0x00000000)):
            addr = 256 + 16 * i
            uc = new_uc(text, base)
            uc.reg_write(UC_ARM_REG_R0, addr)
            uc.reg_write(UC_ARM_REG_S0, b)
            uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
            uc.emu_start(syms["mix_store"] | 1, 0x38000, count=200)
            got = struct.unpack("<I", uc.mem_read(MEMBASE + addr, 4))[0]
            exp["mix_store"](store, addr, bits_f32(b))
            want = struct.unpack("<I", mem.read(store, addr, addr + 4))[0]
            checked += 1
            if got != want or got != b:
                nonlocal_fail(f"mix_store[{addr}]=0x{b:08x} -> mem 0x{got:08x} "
                              f"!= wasmtime 0x{want:08x}")
            else:
                print(f"[mix_store] mem[{addr}] = 0x{got:08x} OK")

    # mix_add(i32 dummy, f32 x, f32 y) -> f32 (x + y); x in S0, y in S1, result S0.
    if need("mix_add"):
        for xb, yb in ((0x3FC00000, 0x40000000), (0x7F800000, 0x3F800000),
                       (0x00000000, 0x80000000)):
            uc = run(text, base, syms["mix_add"], r0=0, s0=xb, s1=yb)
            got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
            want = f32_bits(exp["mix_add"](store, 0, bits_f32(xb), bits_f32(yb)))
            checked += 1
            if got != want:
                nonlocal_fail(f"mix_add(0x{xb:08x},0x{yb:08x}) -> 0x{got:08x} "
                              f"!= wasmtime 0x{want:08x}")
            else:
                print(f"[mix_add] (0x{xb:08x},0x{yb:08x}) -> 0x{got:08x} OK")

    # ---- #719 phase 2: f32 live ACROSS an integer call (spill/reload) ------
    # The callee $fhelp has an integer signature but uses VFP internally, so
    # the BL genuinely clobbers the caller's low S-registers -- these cases are
    # non-vacuous at the value level, not just compile-level. NaN-aware compare:
    # xcall/xcall2 do real f32 adds whose NaN payloads are non-deterministic.
    for fn, wname, arity in (("xcall", "xcall", 1), ("xcall2", "xcall2", 1)):
        if not need(fn):
            continue
        for b in EDGE_BITS:
            uc = run(text, base, syms[fn], r0=b, s0=0x7F7FFFFF, s1=0x7F7FFFFF)
            got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            want = exp[wname](store, b) & 0xFFFFFFFF
            checked += 1
            if not f32_bits_eq(got, want):
                nonlocal_fail(f"{fn}(0x{b:08x}) -> 0x{got:08x} != wasmtime 0x{want:08x}")
            else:
                print(f"[{fn}] 0x{b:08x} -> 0x{got:08x} OK (f32 live across bl)")

    # xhome(f32 x, i32 b): the f32 PARAM HOME S0 must survive the call. S1..
    # poisoned so a wrong reload source shows up.
    if need("xhome"):
        for xb, b in ((0x3FC00000, 0x40000000), (0x80000001, 0x7F800000),
                      (0xC2F60000, 0x00000001)):
            uc = run(text, base, syms["xhome"], r0=b, s0=xb, s1=0xDEADBEEF)
            got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            want = exp["xhome"](store, bits_f32(xb), b) & 0xFFFFFFFF
            checked += 1
            if got != want:
                nonlocal_fail(f"xhome(0x{xb:08x},0x{b:08x}) -> 0x{got:08x} "
                              f"!= wasmtime 0x{want:08x}")
            else:
                print(f"[xhome] (0x{xb:08x},0x{b:08x}) -> 0x{got:08x} OK "
                      f"(param home across bl)")

    # ---- #719 phase 2: float-signature callees must DECLINE (skip), never
    # miscompile: their symbols must be ABSENT from the symtab.
    for fn in ("bad_ret_f32_call", "bad_f32_arg_call"):
        checked += 1
        if fn in syms:
            nonlocal_fail(f"{fn} COMPILED -- a float-signature call boundary "
                          f"must decline loudly (S0/D0 not marshalled)")
        else:
            print(f"[{fn}] absent from symtab OK (loud decline)")

    if fails:
        sys.exit(f"\nFAIL: {fails}/{checked} f32 #719 results diverged")
    print(f"\nGREEN: {checked}/{checked} f32 #719 results bit-exact vs wasmtime "
          f"(abs/neg/copysign/store/local.set/tee + mixed AAPCS-VFP params + "
          f"phase-2 f32-across-call spill/reload; m3 honest-reject + "
          f"float-signature-callee loud-decline confirmed).")


if __name__ == "__main__":
    main()
