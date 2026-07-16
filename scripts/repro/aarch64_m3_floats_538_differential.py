#!/usr/bin/env python3
"""#538 milestone-3 — validate the aarch64 SCALAR-FLOAT backend codegen.

Compiles the m3 float acceptance module with `synth compile -b aarch64`, then
executes each exported function's emitted A64 `.text` two ways —
  (1) under unicorn (UC_ARCH_ARM64, with FPEN enabled so V-register ops run), and
  (2) NATIVELY on the arm64 host (mmap+mprotect the `.text`, call it via a
      ctypes CFUNCTYPE with the right float/int arg + return signature),
and diffs BOTH against wasmtime ground truth. This is the "third backend = third
oracle" property extended to scalar float: f32/f64 add/sub/mul/div, abs/neg/sqrt,
the full compare family (with NaN inputs — the ordering edge cases), the
f32<->f64 promote/demote conversions, the i32->float conversions, and the
f32<->i32 reinterprets.

Float results are compared BIT-EXACTLY (via the raw bit pattern), so a wrong sign
of zero or a mis-rounded conversion is caught; NaN results compare equal iff both
are NaN (WASM does not pin the NaN payload, and neither does the hardware, so a
canonical-vs-arithmetic NaN payload difference is not a bug).

SOUNDNESS: the trapping float->int truncations are NOT in the module — the m3
selector loud-declines them (A64 saturates where WASM traps, #709). That decline
is asserted in the backend unit tests, not here.

Run (needs wasmtime + unicorn + pyelftools; native path needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_m3_floats_538_differential.py
"""
import ctypes
import math
import mmap
import os
import platform
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_CPACR_EL1,
    UC_ARM64_REG_D0,
    UC_ARM64_REG_LR,
    UC_ARM64_REG_S0,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_V0,
    UC_ARM64_REG_V1,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
)

WAT = Path(__file__).with_name("aarch64_m3_floats_538.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
V_ARGS = [UC_ARM64_REG_V0, UC_ARM64_REG_V1]
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1

# Signatures: (fn, [arg_types], ret_type). Types: "f32","f64","i32".
SIGS = {
    "f32_add": (["f32", "f32"], "f32"),
    "f32_sub": (["f32", "f32"], "f32"),
    "f32_mul": (["f32", "f32"], "f32"),
    "f32_div": (["f32", "f32"], "f32"),
    "f32_abs": (["f32"], "f32"),
    "f32_neg": (["f32"], "f32"),
    "f32_eq": (["f32", "f32"], "i32"),
    "f32_ne": (["f32", "f32"], "i32"),
    "f32_lt": (["f32", "f32"], "i32"),
    "f32_le": (["f32", "f32"], "i32"),
    "f32_gt": (["f32", "f32"], "i32"),
    "f32_ge": (["f32", "f32"], "i32"),
    "f64_add": (["f64", "f64"], "f64"),
    "f64_sub": (["f64", "f64"], "f64"),
    "f64_mul": (["f64", "f64"], "f64"),
    "f64_div": (["f64", "f64"], "f64"),
    "f64_abs": (["f64"], "f64"),
    "f64_neg": (["f64"], "f64"),
    "f64_sqrt": (["f64"], "f64"),
    "f64_eq": (["f64", "f64"], "i32"),
    "f64_ne": (["f64", "f64"], "i32"),
    "f64_lt": (["f64", "f64"], "i32"),
    "f64_le": (["f64", "f64"], "i32"),
    "f64_gt": (["f64", "f64"], "i32"),
    "f64_ge": (["f64", "f64"], "i32"),
    "f64_promote_f32": (["f32"], "f64"),
    "f32_demote_f64": (["f64"], "f32"),
    "f32_convert_i32_s": (["i32"], "f32"),
    "f32_convert_i32_u": (["i32"], "f32"),
    "f64_convert_i32_s": (["i32"], "f64"),
    "f64_convert_i32_u": (["i32"], "f64"),
    "f32_reinterpret_i32": (["i32"], "f32"),
    "i32_reinterpret_f32": (["f32"], "i32"),
    "mixed_params": (["i32", "f32", "i32"], "f32"),
}

# Interesting float inputs (as python floats, or ints for i32 args).
F32_PAIRS = [
    (1.5, 2.25), (-3.0, 4.0), (0.0, -0.0), (1.0, 0.0), (-1.0, 0.0),
    (float("inf"), 1.0), (float("nan"), 1.0), (1.0, float("nan")),
    (float("nan"), float("nan")), (3.14159, 2.71828),
    (1e30, 1e30), (-1e30, 2.0), (float("-inf"), float("inf")),
]
F64_PAIRS = F32_PAIRS
I32_VALS = [0, 1, -1, 2147483647, -2147483648, 0x3F800000, 0xC0000000, 42]


def cases_for(fn):
    args, _ = SIGS[fn]
    out = []
    if args == ["f32", "f32"] or args == ["f64", "f64"]:
        for a, b in (F32_PAIRS if args[0] == "f32" else F64_PAIRS):
            out.append([a, b])
    elif args == ["f32"] or args == ["f64"]:
        vals = [x for p in F32_PAIRS for x in p]
        for v in vals:
            out.append([v])
    elif args == ["i32"]:
        for v in I32_VALS:
            out.append([v])
    elif args == ["i32", "f32", "i32"]:
        for v in [1.5, -2.0, 0.0, float("nan"), float("inf")]:
            out.append([7, v, 9])
    return out


# --------------------------------------------------------------------------- #
# encoding helpers
def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def i32_bits(x):
    return x & M32


def as_i32(x):
    """Interpret x's low 32 bits as a signed int (wasmtime/ctypes want signed)."""
    return struct.unpack("<i", struct.pack("<I", int(x) & M32))[0]


def arg_bits(ty, v):
    if ty == "f32":
        return f32_bits(v)
    if ty == "f64":
        return f64_bits(v)
    return i32_bits(int(v))


def is_nan_result(ty, bits):
    if ty == "f32":
        return math.isnan(struct.unpack("<f", struct.pack("<I", bits & M32))[0])
    if ty == "f64":
        return math.isnan(struct.unpack("<d", struct.pack("<Q", bits & M64))[0])
    return False


# --------------------------------------------------------------------------- #
# wasmtime ground truth
def wasmtime_run(fn, args, sig):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, module, []).exports(store)[fn]
    types, ret = sig
    call = []
    for ty, v in zip(types, args):
        call.append(as_i32(v) if ty == "i32" else float(v))
    r = f(store, *call)
    if ret == "f32":
        return f32_bits(r)
    if ret == "f64":
        return f64_bits(r)
    return i32_bits(r)


# --------------------------------------------------------------------------- #
# ELF load
def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        sys.exit(f"aarch64 compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"] & ~1
    return code, base, syms


# --------------------------------------------------------------------------- #
# unicorn execution (FPEN enabled)
def unicorn_run(code, base, faddr, sig, args):
    off = faddr - base
    types, ret = sig
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    # Enable the FP/SIMD unit (FPEN = 0b11 at CPACR_EL1[21:20]); otherwise the
    # first V-register instruction traps.
    mu.reg_write(UC_ARM64_REG_CPACR_EL1, 0x3 << 20)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    ngrn = 0
    nsrn = 0
    for ty, v in zip(types, args):
        b = arg_bits(ty, v)
        if ty in ("f32", "f64"):
            mu.reg_write(V_ARGS[nsrn], b)  # low 32/64 bits of Vn
            nsrn += 1
        else:
            mu.reg_write(X_ARGS[ngrn], b)
            ngrn += 1
    try:
        mu.emu_start(CODE + off, RET, count=2000)
    except UcError as e:
        return f"ERR:{e}"
    if ret == "f32":
        return mu.reg_read(UC_ARM64_REG_S0) & M32
    if ret == "f64":
        return mu.reg_read(UC_ARM64_REG_D0) & M64
    return mu.reg_read(UC_ARM64_REG_W0) & M32


# --------------------------------------------------------------------------- #
# native execution on an arm64 host.
#
# Apple Silicon (darwin/arm64) forbids a plain W+X mapping — JIT pages need
# MAP_JIT plus the per-thread write-protect toggle. Linux/arm64 accepts the
# straightforward RWX mmap. We go through libc mmap directly to pass MAP_JIT.
_native_regions = []

_MAP_PRIVATE = 0x0002
_MAP_ANON = 0x1000 if sys.platform == "darwin" else 0x20
_MAP_JIT = 0x0800  # darwin only
_PROT_RWX = 0x1 | 0x2 | 0x4


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
    if addr == ctypes.c_void_p(-1).value or addr == 0:
        err = ctypes.get_errno()
        raise OSError(err, f"mmap(MAP_JIT) failed: {os.strerror(err)}")
    if sys.platform == "darwin":
        # Enter write mode, copy, then flip to execute mode + flush I-cache.
        wp = ctypes.CDLL(None).pthread_jit_write_protect_np
        wp(0)  # writable
    ctypes.memmove(addr, code, len(code))
    if sys.platform == "darwin":
        wp(1)  # executable
        libc.sys_icache_invalidate.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
        libc.sys_icache_invalidate(ctypes.c_void_p(addr), len(code))
    _native_regions.append((addr, size))
    return addr


_CTY = {"f32": ctypes.c_float, "f64": ctypes.c_double, "i32": ctypes.c_int32}


def native_run(base_addr, faddr, code_base, sig, args):
    types, ret = sig
    fn_addr = base_addr + (faddr - code_base)
    argtypes = [_CTY[t] for t in types]
    restype = _CTY[ret]
    proto = ctypes.CFUNCTYPE(restype, *argtypes)
    fn = proto(fn_addr)
    call = []
    for ty, v in zip(types, args):
        call.append(as_i32(v) if ty == "i32" else float(v))
    r = fn(*call)
    if ret == "f32":
        return f32_bits(r)
    if ret == "f64":
        return f64_bits(r)
    return i32_bits(r)


# --------------------------------------------------------------------------- #
def main():
    out = "/tmp/aarch64_m3_538.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    host_native = platform.machine() in ("arm64", "aarch64")
    native_base = native_setup(code) if host_native else None

    fails = 0
    total = 0
    checked_native = 0
    missing = set()
    for fn, sig in SIGS.items():
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing")
            missing.add(fn)
            fails += 1
            continue
        _, ret = sig
        for args in cases_for(fn):
            total += 1
            exp = wasmtime_run(fn, args, sig)
            uni = unicorn_run(code, base, syms[fn], sig, args)
            oracles = [("unicorn", uni)]
            if host_native:
                nat = native_run(native_base, syms[fn], base, sig, args)
                oracles.append(("native", nat))
                checked_native += 1
            for label, got in oracles:
                if not isinstance(got, int):
                    fails += 1
                    print(f"BUG {fn}{args} [{label}] {got} wasmtime={exp:#x}")
                    continue
                exp_nan = is_nan_result(ret, exp)
                got_nan = is_nan_result(ret, got)
                ok = (exp_nan and got_nan) or (got == exp)
                if not ok:
                    fails += 1
                    print(f"BUG {fn}{args} [{label}] A64={got:#x} "
                          f"wasmtime={exp:#x}")
    print(f"\n{total} wasmtime cases, {checked_native} also run natively "
          f"({'arm64 host' if host_native else 'unicorn-only host'})")
    print(f"{total - (fails if fails <= total else total)}/{total} matched")
    print("RESULT:", "PASS — aarch64 m3 float codegen matches wasmtime "
          "(native + unicorn, third oracle)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
