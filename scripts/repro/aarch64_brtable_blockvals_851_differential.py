#!/usr/bin/env python3
# ci-status: wired
"""VCR-A64-CF-001 (#851) — aarch64 `br_table` + VALUE-CARRYING block/loop/if.

Both constructs used to compile to NOTHING on `-b aarch64`: `br_table` had no
selector arm, and any `(result T)` frame was loud-declined for want of
result-register reconciliation. This harness proves the new lowering EXECUTES
bit-identically to wasmtime.

WHAT MAKES IT NON-VACUOUS.

  * `br_table` is a compare-and-branch CHAIN, so a wrong destination is a wrong
    RESULT, not a slower one. The index lattice is walked per table: every
    in-range arm, the index exactly AT the bound, one OVER it, and 0xFFFFFFFF —
    the case a SIGNED compare would send to the wrong arm, since WASM reads the
    index UNSIGNED and everything out of range must reach the DEFAULT.
  * Two tables put the enclosing LOOP HEADER in the table — once as the default
    (backward) and once as target 0 (the eager `cbz` form) — mixed with a
    forward block end in the SAME table. A lowering that assumed one branch
    direction emits a wrong offset for the other, and the trip count is
    data-dependent, so it shows up as a wrong count.
  * A table at exactly BR_TABLE_MAX_TARGETS (16) walks the whole chain,
    including its last compare.
  * A `br_table` arm that falls into `unreachable` gives a TRAP case: a
    dispatch landing on the wrong arm returns a value where wasmtime traps.
  * For the value-carrying frames, every function is driven down BOTH edges of
    its join (the `br_if` edge and the fall-through), so a lowering that
    reconciled only one of them returns the other path's register.
  * `loop_value` is the SOUNDNESS-CRITICAL shape: a `br` to a LOOP label
    carries the loop's PARAMETERS, not its results, so the back-edge must
    reconcile NOTHING. An implementation that treated "the frame has a result"
    as "reconcile on every branch to it" stamps a garbage value into the result
    register each iteration — which this test's data-dependent trip counts turn
    into a wrong answer.
  * i64 / f64 / f32 results go through the same slot, proving the `mov x` /
    `fmov d` width claims (an f32 carried through the 64-bit FP move must keep
    its single-precision bit pattern).

Two oracles: unicorn (UC_ARCH_ARM64, FPEN enabled) always, and — on an arm64
host — NATIVE execution in a forked child, where an expected `brk #0` is
observed by the parent as SIGTRAP. Memory-using functions run under unicorn
only (the `x28` linear-memory base cannot be established through ctypes).

Run (needs wasmtime + unicorn + pyelftools; native path needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_brtable_blockvals_851_differential.py
"""

import ctypes
import math
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
    UC_ARM64_REG_X2,
    UC_ARM64_REG_X28,
)

WAT = Path(__file__).with_name("aarch64_brtable_blockvals_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
LINMEM, LINMEM_SIZE = 0x1000000, 0x20000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]
V_ARGS = [UC_ARM64_REG_V0, UC_ARM64_REG_V1]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
TRAP = "TRAP"

# fn -> ([param types], result type). AAPCS64 assigns integer and float args
# from INDEPENDENT counters, which the runners below mirror.
SIGS = {
    "switch3": (["i32"], "i32"),
    "default_only": (["i32"], "i32"),
    "dup_targets": (["i32"], "i32"),
    "table_loop_default_back": (["i32"], "i32"),
    "table_loop_target0_back": (["i32"], "i32"),
    "switch16": (["i32"], "i32"),
    "table_trap": (["i32"], "i32"),
    "block_two_edges": (["i32", "i32", "i32"], "i32"),
    "block_nested_br": (["i32", "i32"], "i32"),
    "if_value": (["i32", "i32", "i32"], "i32"),
    "loop_value": (["i32"], "i32"),
    "nested_value_frames": (["i32"], "i32"),
    "block_i64": (["i32", "i64", "i64"], "i64"),
    "block_f64": (["i32", "f64", "f64"], "f64"),
    "block_f32": (["i32", "f32", "f32"], "f32"),
    "block_from_memory": (["i32"], "i32"),
    "block_branch_only": (["i32"], "i32"),
}

# Functions that read/write linear memory: unicorn only (x28 precondition).
MEM_FNS = {"block_from_memory"}

# The index lattice every table is walked over. 0..n-1 are the real arms; n is
# exactly AT the bound; n+1 is over it; 0xFFFFFFFF is the unsigned-index case a
# SIGNED compare chain would mis-dispatch.
CASES = []
for i in [0, 1, 2, 3, 4, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF]:
    CASES.append(("switch3", [i]))
    CASES.append(("default_only", [i]))
    CASES.append(("dup_targets", [i]))
    CASES.append(("table_trap", [i]))
for i in [0, 1, 7, 8, 15, 16, 17, 0xFFFFFFFF, 0x80000000]:
    CASES.append(("switch16", [i]))
# Loop-carrying tables: 0 (immediate exit), 1, and multi-iteration counts.
for n in [0, 1, 2, 5, 37, 0xFFFFFFFF]:
    CASES.append(("table_loop_default_back", [n]))
    CASES.append(("table_loop_target0_back", [n]))
# Value-carrying frames — BOTH edges of every join.
CASES += [
    ("block_two_edges", [1, 7, 9]),          # br_if taken   -> 7 + 1000
    ("block_two_edges", [0, 7, 9]),          # fall-through  -> 9 + 1000
    ("block_two_edges", [0xFFFFFFFF, 3, 4]), # any nonzero cond
    ("block_nested_br", [0, 55]),            # inner br_if taken -> -5
    ("block_nested_br", [1, 55]),            # br 1 (depth-1) -> 55
    ("if_value", [1, 5, 100]),               # then-arm -> 15
    ("if_value", [0, 5, 100]),               # else-arm -> 93
    ("if_value", [0x80000000, 5, 100]),      # nonzero high bit -> then
    ("loop_value", [0]),                     # loop body runs once (do-while)
    ("loop_value", [1]),
    ("loop_value", [5]),
    ("loop_value", [100]),
    ("nested_value_frames", [0]),
    ("nested_value_frames", [1]),
    ("nested_value_frames", [2]),
    ("nested_value_frames", [9]),
    ("block_i64", [1, 0x0123456789ABCDEF, 7]),
    ("block_i64", [0, 0x0123456789ABCDEF, 7]),
    ("block_i64", [0, 1, 0xFFFFFFFFFFFFFFFF]),
    ("block_f64", [1, 1.5, -2.25]),
    ("block_f64", [0, 1.5, -2.25]),
    ("block_f64", [0, 1.5, float("nan")]),
    ("block_f64", [1, -0.0, 3.0]),
    ("block_f32", [1, 1.5, -2.25]),
    ("block_f32", [0, 1.5, -2.25]),
    ("block_f32", [1, -0.0, 3.0]),
    ("block_f32", [0, 2.0, float("inf")]),
    ("block_from_memory", [1]),
    ("block_from_memory", [0]),
    ("block_branch_only", [1]),              # branch edge -> 77
    ("block_branch_only", [0]),              # fall-through is `unreachable`
]


# --------------------------------------------------------------------------- #
def as_signed(ty, v):
    if ty == "i32":
        return struct.unpack("<i", struct.pack("<I", int(v) & M32))[0]
    if ty == "i64":
        return struct.unpack("<q", struct.pack("<Q", int(v) & M64))[0]
    return float(v)


def arg_bits(ty, v):
    if ty == "i32":
        return int(v) & M32
    if ty == "i64":
        return int(v) & M64
    if ty == "f32":
        return struct.unpack("<I", struct.pack("<f", float(v)))[0]
    return struct.unpack("<Q", struct.pack("<d", float(v)))[0]


def result_bits(ty, r):
    if ty == "f32":
        return struct.unpack("<I", struct.pack("<f", float(r)))[0]
    if ty == "f64":
        return struct.unpack("<Q", struct.pack("<d", float(r)))[0]
    return int(r) & (M32 if ty == "i32" else M64)


def is_nan(ty, bits):
    if ty == "f32":
        return math.isnan(struct.unpack("<f", struct.pack("<I", bits & M32))[0])
    if ty == "f64":
        return math.isnan(struct.unpack("<d", struct.pack("<Q", bits & M64))[0])
    return False


# --------------------------------------------------------------------------- #
def wasmtime_run(fn, args, sig):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, module, []).exports(store)[fn]
    types, ret = sig
    call = [as_signed(t, v) for t, v in zip(types, args)]
    try:
        r = f(store, *call)
    except wasmtime.Trap:
        return TRAP
    return result_bits(ret, r)


def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"aarch64 compile failed/skipped: {r.stderr}")


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


def unicorn_run(code, base, faddr, sig, args):
    off = faddr - base
    types, ret = sig
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.reg_write(UC_ARM64_REG_CPACR_EL1, 0x3 << 20)  # FPEN
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_map(LINMEM, LINMEM_SIZE)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mu.reg_write(UC_ARM64_REG_X28, LINMEM)  # the linear-memory base convention
    ngrn = nsrn = 0
    for ty, v in zip(types, args):
        if ty in ("f32", "f64"):
            mu.reg_write(V_ARGS[nsrn], arg_bits(ty, v))
            nsrn += 1
        else:
            mu.reg_write(X_ARGS[ngrn], arg_bits(ty, v))
            ngrn += 1
    try:
        # The trip counts here are bounded by the case table; a runaway branch
        # (the failure mode a wrong back-edge offset produces) hits the cap and
        # is reported as a mismatch rather than hanging the gate.
        mu.emu_start(CODE + off, RET, count=2_000_000)
    except UcError:
        return TRAP  # the guarded `brk #0` — a trap, not a value
    if ret == "f32":
        return mu.reg_read(UC_ARM64_REG_S0) & M32
    if ret == "f64":
        return mu.reg_read(UC_ARM64_REG_D0) & M64
    if ret == "i64":
        return mu.reg_read(UC_ARM64_REG_X0) & M64
    return mu.reg_read(UC_ARM64_REG_W0) & M32


# ---- native arm64 execution (forked child; SIGTRAP == trap) ---------------
_MAP_PRIVATE = 0x0002
_MAP_ANON = 0x1000 if sys.platform == "darwin" else 0x20
_MAP_JIT = 0x0800
_PROT_RWX = 0x1 | 0x2 | 0x4
_CTY = {
    "i32": ctypes.c_int32,
    "i64": ctypes.c_int64,
    "f32": ctypes.c_float,
    "f64": ctypes.c_double,
}


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


def native_run(code, faddr, code_base, sig, args):
    types, ret = sig
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:
        try:
            os.close(rd)
            base_addr = native_setup(code)
            fn = ctypes.CFUNCTYPE(_CTY[ret], *[_CTY[t] for t in types])(
                base_addr + (faddr - code_base)
            )
            r = fn(*[as_signed(t, v) for t, v in zip(types, args)])
            os.write(wr, struct.pack("<Q", result_bits(ret, r)))
            os.close(wr)
        finally:
            os._exit(0)
    os.close(wr)
    _, status = os.waitpid(pid, 0)
    data = os.read(rd, 8)
    os.close(rd)
    if os.WIFSIGNALED(status):
        if os.WTERMSIG(status) in (signal.SIGTRAP, signal.SIGILL):
            return TRAP
        return f"ERR:signal {os.WTERMSIG(status)}"
    if len(data) != 8:
        return "ERR:no result"
    return struct.unpack("<Q", data)[0]


def main():
    out = "/tmp/aarch64_brtable_blockvals_851.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    host_native = platform.machine() in ("arm64", "aarch64")

    fails = 0
    total = 0
    trap_cases = 0
    value_cases = 0
    seen_fns = set()

    for fn, args in CASES:
        sig = SIGS[fn]
        _, ret = sig
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing from the emitted .text — the "
                  f"function was DECLINED, not lowered")
            fails += 1
            continue
        seen_fns.add(fn)
        total += 1
        exp = wasmtime_run(fn, args, sig)
        if exp == TRAP:
            trap_cases += 1
        else:
            value_cases += 1

        oracles = [("unicorn", unicorn_run(code, base, syms[fn], sig, args))]
        if host_native and fn not in MEM_FNS:
            oracles.append(("native", native_run(code, syms[fn], base, sig, args)))

        for label, got in oracles:
            if exp == TRAP or got == TRAP:
                ok = exp == got
            elif not isinstance(got, int):
                ok = False
            elif is_nan(ret, exp):
                # WASM does not pin the NaN payload; NaN == NaN is the contract.
                ok = is_nan(ret, got)
            else:
                ok = got == exp
            if not ok:
                fails += 1
                e = exp if exp == TRAP else hex(exp)
                g = got if isinstance(got, str) else hex(got)
                print(f"BUG {fn}{tuple(str(a) for a in args)} [{label}] "
                      f"A64={g} wasmtime={e}")

    # ---- non-vacuity guards ------------------------------------------------
    missing = set(SIGS) - seen_fns
    if missing:
        print(f"VACUOUS: functions never exercised: {sorted(missing)}")
        fails += 1
    if trap_cases == 0 or value_cases == 0:
        print(f"VACUOUS: trap_cases={trap_cases} value_cases={value_cases} — "
              f"the harness collapsed to one outcome class")
        fails += 1
    if total < 60:
        print(f"VACUOUS: only {total} checks ran; the case lattice shrank")
        fails += 1

    print(f"\n{total} checks ({trap_cases} trap, {value_cases} value) across "
          f"{len(seen_fns)} exported functions, "
          f"{'arm64 host + unicorn' if host_native else 'unicorn-only host'}")
    print("RESULT:", "PASS — aarch64 br_table (index lattice incl. default / "
          "at-bound / over-bound / unsigned 0xFFFFFFFF, mixed loop+block "
          "targets) and value-carrying block/loop/if (both join edges, "
          "i32/i64/f32/f64) match wasmtime"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
