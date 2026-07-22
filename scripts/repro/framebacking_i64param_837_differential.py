#!/usr/bin/env python3
"""#837 — frame-backing i64/f64-param lowering (the last #518 i64-param sub-case).

gale's `gust:os/timer` provider hit a LOUD DECLINE (not a miscompile — the object
was never wrong, the function was just skipped) on a natural shape: a function
whose signature carries a 64-bit VALUE param AND whose body makes a call:

    sleep(handle: u32, ticks: u64) -> u32   # body calls read32(handle) then an
                                            # in-module fn, then USES ticks.

The u64 param arrives in an AAPCS even-aligned register pair (here R2:R3, since a
leading i32 takes R0 and the pair even-aligns past R1). A call reclaims R0..R3 for
its args and clobbers them (caller-saved), so the pair must be HOMED into the
frame in the prologue, survive the call there, and be RELOADED after — exactly the
frame-backing #204/#193 path, which previously sized an i64 param's slot from a
width set (`i64_set`) that excludes params, giving it a 4-byte slot and dropping
the high half. Rather than miscompile, the backend declined by name (#518).

The #837 fix sizes the frame-backing param slot from the DECLARED AAPCS width
(`params_i64`), so R2:R3 is homed as an 8-byte pair (`I64Str`) and reloaded as a
pair (`I64Ldr`) after the call — machinery that was already `is_i64`-aware.

This differential is the red->green EXECUTION oracle: it compiles the in-tree
`framebacking_i64param_837.wat` `--relocatable --target cortex-m3`, resolves the
`R_ARM_THM_CALL` relocations to `read32` (import) and `combine` (in-module),
installs a deterministic `read32` stub, runs `sleep(handle, ticks)` under unicorn
(Thumb-2), and checks the returned u32 equals the reference model over a matrix of
`ticks` values whose HIGH 32 bits are non-zero — so a dropped high half or a
clobbered pair would diverge. A companion `sleep_hi` export mixes BOTH halves of
the u64 into its result, so the FULL pair (not just the low word) must survive.

Reference model (mirrors the wat exactly):
    read32(x)      = x ^ 0xA5A5A5A5            # deterministic mmio stub
    combine(x)     = x + 7                     # in-module fn (result dropped)
    sleep(h, t)    = (low32(t) + read32(h)) & 0xFFFFFFFF
    sleep_hi(h, t) = ((low32(t) ^ high32(t)) + read32(h)) & 0xFFFFFFFF

Run (needs unicorn + pyelftools; wasmtime not required — read32 is a host stub):
  SYNTH=./target/debug/synth python scripts/repro/framebacking_i64param_837_differential.py
"""
import os
import struct
import subprocess
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("framebacking_i64param_837.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

TEXT = 0x100000
STK = 0x900000
RET = 0x300000
READ32_STUB = 0x140000  # deterministic mmio read: read32(x) = x ^ MMIO_XOR
MMIO_XOR = 0xA5A5A5A5

ABS32, THM_CALL = 2, 10

# ticks matrix — HIGH 32 bits non-zero so a dropped hi half still diverges on sleep_hi.
CASES = [
    0x00000000_00000000,
    0x00000000_00000007,
    0xDEADBEEF_00000001,
    0xFFFFFFFF_FFFFFFFF,
    0x12345678_9ABCDEF0,
]


def model_read32(x):
    return (x ^ MMIO_XOR) & 0xFFFFFFFF


def model_sleep(h, t):
    return ((t & 0xFFFFFFFF) + model_read32(h)) & 0xFFFFFFFF


def model_sleep_hi(h, t):
    return (((t & 0xFFFFFFFF) ^ ((t >> 32) & 0xFFFFFFFF)) + model_read32(h)) & 0xFFFFFFFF


def compile_synth(out):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m3", "--all-exports", "--relocatable"]
    return subprocess.run(cmd, capture_output=True, text=True, env=env)


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text_sec = f.get_section_by_name(".text")
    text = bytearray(text_sec.data())
    base = text_sec["sh_addr"]
    st = None
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            st = sec
    syms = {}
    for s in st.iter_symbols():
        if s.name and s["st_info"]["type"] == "STT_FUNC":
            syms[s.name] = s["st_value"]
    return f, st, text, base, syms


def resolve_relocs(f, st, text, base, syms):
    relsec = f.get_section_by_name(".rel.text")
    for r in relsec.iter_relocations():
        t = r["r_info_type"]
        sym = st.get_symbol(r["r_info_sym"])
        off = r["r_offset"]
        if t == THM_CALL:
            S = (READ32_STUB if sym.name == "read32" else TEXT + syms[sym.name]) & ~1
            P = TEXT + off + 4
            disp = S - P
            imm = (disp >> 1) & 0x3FFFFF
            s = (imm >> 21) & 1
            i1 = (imm >> 20) & 1
            i2 = (imm >> 19) & 1
            j1 = (~i1 & 1) ^ s
            j2 = (~i2 & 1) ^ s
            imm10 = (imm >> 11) & 0x3FF
            imm11 = imm & 0x7FF
            hi = 0xF000 | (s << 10) | imm10
            lo = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
            struct.pack_into("<HH", text, off, hi, lo)
        elif t == ABS32:
            (add,) = struct.unpack_from("<I", text, off)
            struct.pack_into("<I", text, off, (TEXT + syms.get(sym.name, 0) + add) & 0xFFFFFFFF)
        else:
            raise SystemExit(f"unhandled reloc type {t} at {off:#x}")


def _movw_movt(rd, imm16, is_movt):
    base_op = 0xF2C0 if is_movt else 0xF240
    i = (imm16 >> 11) & 1
    imm4 = (imm16 >> 12) & 0xF
    imm3 = (imm16 >> 8) & 0x7
    imm8 = imm16 & 0xFF
    w0 = base_op | (i << 10) | imm4
    w1 = (imm3 << 12) | (rd << 8) | imm8
    return struct.pack("<HH", w0, w1)


def build_mu(text):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(TEXT, 0x80000)  # 0x100000..0x180000 — also covers READ32_STUB (0x140000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(TEXT, bytes(text))
    # read32 stub: movw/movt r1,#MMIO_XOR ; eors r0,r1 ; bx lr  (Thumb-2).
    lo = MMIO_XOR & 0xFFFF
    hi = (MMIO_XOR >> 16) & 0xFFFF
    stub = bytearray()
    stub += _movw_movt(1, lo, False)
    stub += _movw_movt(1, hi, True)
    stub += struct.pack("<H", 0x4048)  # eors r0, r1
    stub += struct.pack("<H", 0x4770)  # bx lr
    mu.mem_write(READ32_STUB, bytes(stub))
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")
    return mu


def run(mu, faddr, base, h, t):
    foff = (faddr & ~1) - base
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, 0)
    # AAPCS: (i32, i64) -> h in R0, ticks even-aligned in R2:R3 (R1 skipped).
    mu.reg_write(UC_ARM_REG_R0, h & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, 0xDEAD0000)  # poison the skipped R1
    mu.reg_write(UC_ARM_REG_R2, t & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R3, (t >> 32) & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start((TEXT + foff) | 1, RET, count=100000)
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    out = "/tmp/i837.o"
    r = compile_synth(out)
    if r.returncode != 0:
        print(f"RESULT: FAIL — compile errored: {r.stderr}")
        sys.exit(1)
    if "skipping function 'sleep'" in r.stderr:
        print("RESULT: FAIL — 'sleep' (frame-backing i64 param + call) was LOUD-SKIPPED; "
              "the #837 lowering did not fire.")
        sys.exit(1)

    f, st, text, base, syms = load(out)
    for need in ("sleep", "sleep_hi", "slept", "combine"):
        if need not in syms:
            print(f"RESULT: FAIL — '{need}' absent from symtab (unexpected skip).")
            sys.exit(1)
    resolve_relocs(f, st, text, base, syms)
    mu = build_mu(text)

    fails = 0
    H = 0x0000_0011
    print("=== sleep(handle, ticks) — low32(ticks)+read32(handle), u64 param survives call ===")
    for t in CASES:
        exp = model_sleep(H, t)
        try:
            got = run(mu, syms["sleep"], base, H, t)
        except UcError as e:
            got = f"ERR:{e}"
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        print(f"  [{'ok ' if ok else 'BUG'}] sleep(h={H:#x}, ticks={t:#018x}) -> "
              f"{got if isinstance(got, str) else hex(got)}  (model {hex(exp)})")

    print("=== sleep_hi — result mixes BOTH halves of the u64 param (full pair must survive) ===")
    for t in CASES:
        exp = model_sleep_hi(H, t)
        try:
            got = run(mu, syms["sleep_hi"], base, H, t)
        except UcError as e:
            got = f"ERR:{e}"
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        print(f"  [{'ok ' if ok else 'BUG'}] sleep_hi(h={H:#x}, ticks={t:#018x}) -> "
              f"{got if isinstance(got, str) else hex(got)}  (model {hex(exp)})")

    print("\n--- verdict ---")
    if fails == 0:
        print("RESULT: PASS — the frame-backing i64/f64-param-with-call shape (gale's "
              "gust:os/timer sleep) is LOWERED and the u64 value param survives the "
              "call bit-identically to the reference model (#837 fixed, #518 class "
              "complete for the register-resident case).")
        sys.exit(0)
    print(f"RESULT: FAIL — {fails} divergence(s); the u64 param did not survive the call.")
    sys.exit(1)


if __name__ == "__main__":
    main()
