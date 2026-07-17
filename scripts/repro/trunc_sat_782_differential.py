#!/usr/bin/env python3
"""#782a — the trunc_sat (nontrapping saturating float->int) boundary
EXECUTION differential.

WASM §4.3.2 trunc_sat is TOTAL: NaN -> 0, below INT_MIN -> INT_MIN, above
INT_MAX -> INT_MAX (unsigned: negatives -> 0, above UINT_MAX -> UINT_MAX),
else truncate toward zero. NO traps — anywhere. The lowerings under test:

  * ARM32 Thumb-2 (cortex-m7dp, falcon's #782 target): the i32-target quartet
    as a BARE round-toward-zero VCVT (which saturates and yields 0 for NaN —
    exactly trunc_sat; the very behavior the #709 guard keeps away from the
    TRAPPING forms). The i64-target quartet LOUD-declines (no i64
    register-pair conversion path) — asserted here, symbols must be absent
    and the decline must be named.
  * aarch64: all eight via bare FCVTZS/FCVTZU (w and x destinations).

Every boundary case must match wasmtime bit-exactly AND must not trap on our
side (a UDF/brk stop is a failure by construction); wasmtime itself is
asserted total first, so the table cannot drift vacuous. The falcon repro
flags (`-t cortex-m7dp --relocatable`) are compile-gated: the four i32-target
exports must NOT be skipped (the #782 'skipping ts32/ts64' class), the four
i64-target exports MUST still be skipped loudly (decline-honesty).

Run (needs wasmtime + unicorn + pyelftools; native path needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/trunc_sat_782_differential.py
"""

import ctypes
import os
import platform
import signal
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_ARCH_ARM64, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_CPACR_EL1,
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_V0,
    UC_ARM64_REG_X0,
)
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_LR,
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

WAT = Path(__file__).with_name("trunc_sat_782.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
MEMBASE = 0x20000000  # ARM32 R11/fp linear-memory base at reset (cortex_m.rs)
A64_CODE, A64_STK, A64_RET = 0x100000, 0x200000, 0x300000

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
INF = float("inf")
NAN = float("nan")

I32_FNS = {
    "i32_trunc_sat_f32_s": ("f32", "i32"),
    "i32_trunc_sat_f32_u": ("f32", "i32"),
    "i32_trunc_sat_f64_s": ("f64", "i32"),
    "i32_trunc_sat_f64_u": ("f64", "i32"),
}
I64_FNS = {
    "i64_trunc_sat_f32_s": ("f32", "i64"),
    "i64_trunc_sat_f32_u": ("f32", "i64"),
    "i64_trunc_sat_f64_s": ("f64", "i64"),
    "i64_trunc_sat_f64_u": ("f64", "i64"),
}
SIGS = {**I32_FNS, **I64_FNS}

# ---------------------------------------------------------------------------
# The §4.3.2 boundary table. EVERY case is total (wasmtime asserted no-trap):
# NaN, ±inf, the exact saturation boundaries on both sides, ±0.5 fractions,
# and plain in-range values. Boundary subtleties pinned:
#   - f32 can't represent 2^31-1: 2147483520.0 is the largest f32 < 2^31;
#     2^31 itself (2147483648.0) saturates to INT32_MAX. -2^31 is exact and
#     in-range; the next f32 below (-2147483904.0) saturates to INT32_MIN.
#   - f64->i32: 2147483647.9 truncates to INT32_MAX in-range; 2147483648.0
#     saturates. -2147483648.999 truncates to -2^31; -2147483649.0 saturates.
#   - unsigned: (-1.0, -0.0] truncates to 0 in-range semantics anyway; any
#     value <= -1.0 (and -inf, NaN) must yield 0.
#   - f32/f64->i64: 2^63 saturates to INT64_MAX (no f32/f64 hits 2^63-1);
#     -2^63 is exactly representable and in-range for _s.
BOUNDARY = {
    "f32": [
        0.0, -0.0, 0.5, -0.5, 0.9, -0.9, 1.5, -1.5, 42.0, -42.0, 100.75,
        2147483520.0, -2147483520.0, 2147483648.0, -2147483648.0,
        2147483904.0, -2147483904.0, 4294967040.0, 4294967296.0,
        -1.0, -1.5, 3e9, -3e9, 5e9, 1e10, -1e10,
        9223371487098961920.0,   # largest f32 < 2^63
        9223372036854775808.0,   # 2^63: i64_s saturates to INT64_MAX
        -9223372036854775808.0,  # -2^63 exactly: i64_s in-range minimum
        18446742974197923840.0,  # largest f32 < 2^64
        18446744073709551616.0,  # 2^64: i64_u saturates to UINT64_MAX
        1e30, -1e30, INF, -INF, NAN,
    ],
    "f64": [
        0.0, -0.0, 0.5, -0.5, 0.9, -0.9, 1.5, -1.5, 42.0, -42.0, 100.75,
        2147483647.0, 2147483647.9, 2147483648.0, 2147483648.5,
        -2147483648.0, -2147483648.5, -2147483648.999,
        -2147483649.0, -2147483649.5,
        4294967295.0, 4294967295.9, 4294967296.0, 4294967296.5,
        -1.0, -1.5, 1e18, -1e18,
        9223372036854774784.0,   # largest f64 < 2^63
        9223372036854775808.0,   # 2^63: i64_s saturates
        -9223372036854775808.0,  # -2^63 exactly: i64_s in-range minimum
        -9223372036854777856.0,  # first f64 below -2^63: i64_s saturates
        18446744073709549568.0,  # largest f64 < 2^64
        18446744073709551616.0,  # 2^64: i64_u saturates
        1e300, -1e300, INF, -INF, NAN,
    ],
}


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def arg_bits(ty, v):
    return f32_bits(v) if ty == "f32" else f64_bits(v)


# ---------------------------------------------------------------------------
# wasmtime ground truth — trunc_sat is TOTAL, so a wasmtime trap is a
# harness/fixture bug, not a data point.
def wasmtime_expected():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    exports = wasmtime.Instance(store, module, []).exports(store)
    table = {}
    for fn, (aty, rty) in SIGS.items():
        f = exports[fn]
        rows = []
        for v in BOUNDARY[aty]:
            try:
                r = f(store, float(v))
            except wasmtime.Trap:
                sys.exit(f"TABLE-BUG: wasmtime TRAPPED on {fn}({v!r}) — "
                         f"trunc_sat must be total")
            rows.append((v, int(r) & (M32 if rty == "i32" else M64)))
        table[fn] = rows
    return table


# ---------------------------------------------------------------------------
def compile_or_die(out, extra, what):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, *extra]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        sys.exit(f"{what} compile failed: {r.stderr}")
    return r.stderr + r.stdout


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


# ---------------------------------------------------------------------------
# ARM32 (Thumb-2) unicorn execution. Returns ('ok', r0) or ('trap', pc-info).
def arm32_run(text, base, addr, aty, v):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    map_base = base & ~0xFFF
    size = ((len(text) + (base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(base, text)
    uc.mem_map(0x30000, 0x10000)  # stack
    uc.mem_map(MEMBASE, 0x10000)  # linear-memory window (R11 base)
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    uc.reg_write(UC_ARM_REG_R11, MEMBASE)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)  # CPACR CP10/CP11
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)  # FPEXC.EN
    if aty == "f32":
        uc.reg_write(UC_ARM_REG_S0, f32_bits(v))
    else:
        uc.reg_write(UC_ARM_REG_D0, f64_bits(v))
    ret = 0x38000
    uc.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        uc.emu_start(addr | 1, ret & ~1, count=500)
    except UcError as e:
        pc = uc.reg_read(UC_ARM_REG_PC)
        kind = "fault"
        if base <= pc < base + len(text):
            hw = struct.unpack("<H", text[pc - base: pc - base + 2])[0]
            if hw & 0xFF00 == 0xDE00:  # Thumb UDF
                kind = "trap-udf"
        return (kind, f"{e} at pc={pc:#x}")
    return ("ok", uc.reg_read(UC_ARM_REG_R0) & M32)


# ---------------------------------------------------------------------------
# aarch64 unicorn execution. Returns ('ok', bits) or ('trap', msg).
def a64_run(code, base, faddr, aty, rty, v):
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.reg_write(UC_ARM64_REG_CPACR_EL1, 0x3 << 20)  # FPEN
    mu.mem_map(A64_CODE, 0x20000)
    mu.mem_map(A64_STK - 0x10000, 0x20000)
    mu.mem_map(A64_RET & ~0xFFF, 0x1000)
    mu.mem_write(A64_CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, A64_STK)
    mu.reg_write(UC_ARM64_REG_LR, A64_RET)
    mu.reg_write(UC_ARM64_REG_V0, arg_bits(aty, v))
    try:
        mu.emu_start(A64_CODE + (faddr - base), A64_RET, count=2000)
    except UcError as e:
        return ("trap", str(e))
    x0 = mu.reg_read(UC_ARM64_REG_X0)
    return ("ok", x0 & (M32 if rty == "i32" else M64))


# ---------------------------------------------------------------------------
# native aarch64 execution (arm64 host): forked child, SIGTRAP observable.
_MAP_PRIVATE = 0x0002
_MAP_ANON = 0x1000 if sys.platform == "darwin" else 0x20
_MAP_JIT = 0x0800
_PROT_RWX = 0x1 | 0x2 | 0x4
_CTY = {"f32": ctypes.c_float, "f64": ctypes.c_double,
        "i32": ctypes.c_int32, "i64": ctypes.c_int64}


def native_setup(code):
    libc = ctypes.CDLL(None, use_errno=True)
    libc.mmap.restype = ctypes.c_void_p
    libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int,
                          ctypes.c_int, ctypes.c_int, ctypes.c_long]
    size = max(len(code), 4096)
    flags = _MAP_PRIVATE | _MAP_ANON
    if sys.platform == "darwin":
        flags |= _MAP_JIT
    addr = libc.mmap(None, size, _PROT_RWX, flags, -1, 0)
    if addr in (ctypes.c_void_p(-1).value, 0, None):
        err = ctypes.get_errno()
        raise OSError(err, f"mmap(MAP_JIT) failed: {os.strerror(err)}")
    if sys.platform == "darwin":
        wp = ctypes.CDLL(None).pthread_jit_write_protect_np
        wp(0)
    ctypes.memmove(addr, code, len(code))
    if sys.platform == "darwin":
        wp(1)
        libc.sys_icache_invalidate.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
        libc.sys_icache_invalidate(ctypes.c_void_p(addr), len(code))
    return addr


def native_run(code, faddr, code_base, aty, rty, v):
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:  # child
        try:
            os.close(rd)
            base_addr = native_setup(code)
            proto = ctypes.CFUNCTYPE(_CTY[rty], _CTY[aty])
            fn = proto(base_addr + (faddr - code_base))
            r = fn(float(v))  # any brk -> SIGTRAP -> child dies
            bits = int(r) & (M32 if rty == "i32" else M64)
            os.write(wr, struct.pack("<Q", bits))
            os.close(wr)
        finally:
            os._exit(0)
    os.close(wr)
    _, status = os.waitpid(pid, 0)
    data = os.read(rd, 8)
    os.close(rd)
    if os.WIFSIGNALED(status):
        sig_no = os.WTERMSIG(status)
        if sig_no in (signal.SIGTRAP, signal.SIGILL):
            return ("trap", f"signal {sig_no}")
        return ("trap", f"ERR:signal {sig_no}")
    if len(data) != 8:
        return ("trap", "ERR:no result")
    return ("ok", struct.unpack("<Q", data)[0])


# ---------------------------------------------------------------------------
def main():
    expected = wasmtime_expected()
    fails = 0
    total = 0

    # ==== falcon repro flags (#782): -t cortex-m7dp --relocatable ==========
    # The four i32-target exports must NOT skip; the four i64-target exports
    # MUST still skip with the named ARM32 decline (decline-honesty).
    log = compile_or_die("/tmp/trunc_sat_782_reloc.elf",
                         ["-b", "arm", "--target", "cortex-m7dp",
                          "--relocatable"],
                         "ARM32 --relocatable (falcon flags)")
    for fn in I32_FNS:
        if fn in log and "kipping" in log:
            # cheap guard; the authoritative check is the symbol table below
            pass
    _, _, reloc_syms = load("/tmp/trunc_sat_782_reloc.elf")
    for fn in I32_FNS:
        total += 1
        if fn not in reloc_syms:
            fails += 1
            print(f"FAIL [falcon-flags] {fn}: SKIPPED under "
                  f"-t cortex-m7dp --relocatable (the #782 class)")
    for fn in I64_FNS:
        total += 1
        if fn in reloc_syms:
            fails += 1
            print(f"FAIL [falcon-flags] {fn}: compiled on 32-bit ARM — "
                  f"expected a LOUD decline (no i64 pair conversion)")
    if "register-pair" not in log:
        fails += 1
        print("FAIL [falcon-flags]: the i64 trunc_sat decline is not NAMED "
              "in the compile log (decline-honesty)")

    # ==== ARM32 self-contained (cortex-m7dp): execute the i32 quartet ======
    compile_or_die("/tmp/trunc_sat_782_arm.elf",
                   ["-b", "arm", "--target", "cortex-m7dp", "--all-exports"],
                   "ARM32 cortex-m7dp")
    text, base, syms = load("/tmp/trunc_sat_782_arm.elf")
    for fn, (aty, rty) in I32_FNS.items():
        if fn not in syms:
            fails += 1
            print(f"FAIL [arm32] {fn}: symbol missing")
            continue
        for v, want in expected[fn]:
            total += 1
            kind, got = arm32_run(text, base, syms[fn], aty, v)
            if kind != "ok":
                fails += 1
                print(f"BUG [arm32] {fn}({v!r}) -> {kind}: {got} — trunc_sat "
                      f"must NEVER trap (wasmtime: {want:#x})")
            elif got != want:
                fails += 1
                print(f"BUG [arm32] {fn}({v!r}) = {got:#x} != wasmtime {want:#x}")
    # i64-target forms must be absent (loud-declined) on ARM32 here too.
    for fn in I64_FNS:
        total += 1
        if fn in syms:
            fails += 1
            print(f"FAIL [arm32] {fn}: compiled on 32-bit ARM — expected decline")

    # ==== ARM32 single-precision (cortex-m4f): f32 quartet only ============
    # trunc_sat_f32_* needs only single-precision VFP; the f64-source forms
    # ride the existing double-FPU honest-reject.
    compile_or_die("/tmp/trunc_sat_782_m4f.elf",
                   ["-b", "arm", "--target", "cortex-m4f", "--all-exports"],
                   "ARM32 cortex-m4f")
    m4f_text, m4f_base, m4f_syms = load("/tmp/trunc_sat_782_m4f.elf")
    for fn, (aty, rty) in I32_FNS.items():
        if aty != "f32":
            total += 1
            if fn in m4f_syms:
                fails += 1
                print(f"FAIL [m4f] {fn}: f64 source compiled on a "
                      f"single-precision target — expected decline")
            continue
        if fn not in m4f_syms:
            fails += 1
            print(f"FAIL [m4f] {fn}: symbol missing")
            continue
        for v, want in expected[fn]:
            total += 1
            kind, got = arm32_run(m4f_text, m4f_base, m4f_syms[fn], aty, v)
            if kind != "ok":
                fails += 1
                print(f"BUG [m4f] {fn}({v!r}) -> {kind}: {got}")
            elif got != want:
                fails += 1
                print(f"BUG [m4f] {fn}({v!r}) = {got:#x} != wasmtime {want:#x}")

    # ==== aarch64: all eight, unicorn + native ==============================
    compile_or_die("/tmp/trunc_sat_782_a64.o",
                   ["-b", "aarch64", "--all-exports"], "aarch64")
    a64_code, a64_base, a64_syms = load("/tmp/trunc_sat_782_a64.o")
    host_native = platform.machine() in ("arm64", "aarch64")
    checked_native = 0
    for fn, (aty, rty) in SIGS.items():
        if fn not in a64_syms:
            fails += 1
            print(f"FAIL [a64] {fn}: symbol missing")
            continue
        faddr = a64_syms[fn] & ~1
        for v, want in expected[fn]:
            total += 1
            oracles = [("unicorn", a64_run(a64_code, a64_base, faddr, aty, rty, v))]
            if host_native:
                oracles.append(
                    ("native", native_run(a64_code, faddr, a64_base, aty, rty, v)))
                checked_native += 1
            for label, (kind, got) in oracles:
                if kind != "ok":
                    fails += 1
                    print(f"BUG [a64/{label}] {fn}({v!r}) -> TRAP ({got}) — "
                          f"trunc_sat must NEVER trap (wasmtime: {want:#x})")
                elif got != want:
                    fails += 1
                    print(f"BUG [a64/{label}] {fn}({v!r}) = {got:#x} != "
                          f"wasmtime {want:#x}")

    print(f"\n{total} checks ({checked_native} also run natively, "
          f"{'arm64 host' if host_native else 'unicorn-only host'})")
    print("RESULT:", "PASS — trunc_sat boundary table matches wasmtime on "
          "ARM32(m7dp+m4f)+aarch64; no traps anywhere; ARM32 i64 forms "
          "loud-declined" if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
