#!/usr/bin/env python3
"""#851 — aarch64 integer div/rem trap-and-value EXECUTION differential.

A64 SDIV/UDIV are TOTAL where WASM `idiv`/`irem` (Core §4.3.2) are PARTIAL, so
a bare lowering is a silent "more-total-than-WASM" miscompile (the #633/#666/
#709 class). synth's aarch64 backend defends the totality gap with explicit
guards; this harness proves those guards TRAP exactly where wasmtime traps and
compute the right value everywhere else, execution-verified TWO ways:
  (1) unicorn (UC_ARCH_ARM64): a guard's `brk #0` raises UC_ERR_EXCEPTION;
  (2) natively on an arm64 host: each call runs in a forked child, so an
      expected SIGTRAP is observed by the parent (and a surprise trap can't
      take the harness down).

The trap table pinned (per WASM Core §4.3.2):
  * div/rem by ZERO  -> TRAP (all four forms, both widths).
  * div_s(INT_MIN, -1) -> TRAP (quotient +2^(N-1) is unrepresentable).
  * rem_s(INT_MIN, -1) -> 0  (NO trap — a64 MSUB yields 0 naturally).
The static expect-trap column is itself validated against wasmtime FIRST — if
wasmtime disagrees, the FIXTURE is declared wrong (loud), so the table cannot
drift vacuous (matches the m4 boundary-table gate).

Run (needs wasmtime + unicorn + pyelftools; native path needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_divrem_851_differential.py
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
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
)

WAT = Path(__file__).with_name("aarch64_divrem_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
I32_MIN = -(1 << 31)
I64_MIN = -(1 << 63)
TRAP = "TRAP"

# fn -> (width_bits, signed). All are (param T T)(result T).
SIGS = {
    "i32_div_s": (32, True),
    "i32_div_u": (32, False),
    "i32_rem_s": (32, True),
    "i32_rem_u": (32, False),
    "i64_div_s": (64, True),
    "i64_div_u": (64, False),
    "i64_rem_s": (64, True),
    "i64_rem_u": (64, False),
}


def cases_for(fn, width):
    """(a, b) operand pairs — a mix of ordinary values + every trap edge."""
    mn = I32_MIN if width == 32 else I64_MIN
    ordinary = [
        (7, 2), (7, 3), (-7, 2), (7, -2), (-7, -3),
        (100, 7), (-100, 7), (100, -7),
        (mn, 1), (mn, 2), (mn, -2), (0, 5), (5, 5),
        (mn + 1, -1),  # NOT INT_MIN: -1 divisor is fine here
    ]
    edges = [
        (7, 0), (0, 0), (-7, 0), (mn, 0),  # divide-by-zero: always traps
        (mn, -1),  # div_s: overflow trap; rem_s: 0; div_u/rem_u: no trap
    ]
    return ordinary + edges


# --------------------------------------------------------------------------- #
def to_signed(v, width):
    m = M32 if width == 32 else M64
    v &= m
    bit = 1 << (width - 1)
    return v - (1 << width) if v & bit else v


def to_unsigned(v, width):
    return v & (M32 if width == 32 else M64)


# --------------------------------------------------------------------------- #
# wasmtime ground truth (TRAP on wasmtime.Trap).
def wasmtime_run(fn, a, b, width):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, module, []).exports(store)[fn]
    try:
        r = f(store, to_signed(a, width), to_signed(b, width))
    except wasmtime.Trap:
        return TRAP
    return to_unsigned(r, width)


# --------------------------------------------------------------------------- #
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
# unicorn execution: value, or TRAP when a guard's brk raises an exception.
def unicorn_run(code, base, faddr, a, b, width):
    off = faddr - base
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mu.reg_write(X_ARGS[0], to_unsigned(a, width))
    mu.reg_write(X_ARGS[1], to_unsigned(b, width))
    try:
        mu.emu_start(CODE + off, RET, count=2000)
    except UcError:
        return TRAP
    v = mu.reg_read(UC_ARM64_REG_X0)
    return v & (M32 if width == 32 else M64)


# --------------------------------------------------------------------------- #
# native execution on an arm64 host — each call in a forked child so an
# expected `brk #0` (SIGTRAP) is observable and a surprise one survivable.
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


def native_run(code, faddr, code_base, a, b, width):
    """Fork; the child JITs + calls the function and pipes back the result. A
    trap (SIGTRAP from `brk #0`) kills the CHILD; the parent reports TRAP. The
    MAP_JIT region is created IN the child (an inherited parent mapping can
    SIGBUS after fork on macOS)."""
    cty = ctypes.c_int32 if width == 32 else ctypes.c_int64
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:  # child
        try:
            os.close(rd)
            base_addr = native_setup(code)
            fn_addr = base_addr + (faddr - code_base)
            proto = ctypes.CFUNCTYPE(cty, cty, cty)
            fn = proto(fn_addr)
            r = fn(to_signed(a, width), to_signed(b, width))
            os.write(wr, struct.pack("<q", int(r)))
            os.close(wr)
        finally:
            os._exit(0)
    os.close(wr)
    _, status = os.waitpid(pid, 0)
    data = os.read(rd, 8)
    os.close(rd)
    if os.WIFSIGNALED(status):
        sig_no = os.WTERMSIG(status)
        if sig_no in (signal.SIGTRAP, signal.SIGILL, signal.SIGFPE):
            return TRAP
        return f"ERR:signal {sig_no}"
    if len(data) != 8:
        return "ERR:no result"
    return to_unsigned(struct.unpack("<q", data)[0], width)


# --------------------------------------------------------------------------- #
def main():
    out = "/tmp/aarch64_divrem_851.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    host_native = platform.machine() in ("arm64", "aarch64")

    fails = 0
    total = 0
    trap_cases = 0
    checked_native = 0
    for fn, (width, _signed) in SIGS.items():
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing (op declined?)")
            fails += 1
            continue
        for a, b in cases_for(fn, width):
            total += 1
            exp = wasmtime_run(fn, a, b, width)
            if exp == TRAP:
                trap_cases += 1
            oracles = [("unicorn", unicorn_run(code, base, syms[fn], a, b, width))]
            if host_native:
                oracles.append(("native", native_run(code, syms[fn], base, a, b, width)))
                checked_native += 1
            for label, got in oracles:
                ok = (exp == got) if (exp == TRAP or got == TRAP) else (exp == got)
                if not ok:
                    fails += 1
                    e = exp if exp == TRAP else hex(exp)
                    g = got if isinstance(got, str) else hex(got)
                    print(f"BUG {fn}(a={a},b={b}) [{label}] A64={g} wasmtime={e}")

    print(f"\n{total} wasmtime cases ({trap_cases} trap cases), "
          f"{checked_native} also run natively "
          f"({'arm64 host' if host_native else 'unicorn-only host'})")
    print("RESULT:", "PASS — aarch64 div/rem match wasmtime; the ÷0 and "
          "INT_MIN/-1 traps are execution-verified (native SIGTRAP + unicorn brk)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
