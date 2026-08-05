#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 21
"""#865 — aarch64 linear-memory BOUNDS differential (gale's OOB table).

gale (#865): the v0.51.0 aarch64 lowering emitted NO bounds check and
`--safety-bounds` was a silent no-op — `none|software|mask|mpu` produced
byte-identical objects, and a `(memory 1)` guest could read/write up to
4 GiB past its linear memory (the address is zero-extended, `uxtw`) where
wasmtime traps. This gate reproduces gale's executed table and pins the fix:

1. EXECUTION (unicorn, `(memory 1)` = 64 KiB, host memory beyond the limit
   poisoned with a sentinel):
     - addr 65532 (in-bounds)      → same value as wasmtime
     - addr 65536 / 100000 / -1   → must TRAP (`brk` = UC_ERR_EXCEPTION)
       exactly where wasmtime traps. Pre-fix these return host garbage
       (the poison / an unmapped-fault, NOT a brk) → RED.
   Width + memarg-offset accounting is pinned too: a 4-byte load at 65533
   and an offset=65532 load at addr 4 both straddle the limit → trap;
   a 1-byte load at 65535 is the last in-bounds byte → value.
   The STORE form must trap OOB as well (the arbitrary-write primitive).
2. MODES now DIFFER (the byte-identical-md5 symptom is gone):
     - md5(--safety-bounds none) != md5(--safety-bounds software)
     - flag ABSENT == software (the default ENFORCES — the silent path is
       the checked path)
     - `none` executed at 65536 does NOT brk (the opt-out is real and
       distinct, reads the poison sentinel)
     - mask / mpu → the compile HARD-ERRORS mentioning #865 (never again
       a silently-accepted no-op mode).
3. The SINGLE-FUNCTION path (`-n f`, gale's exact command) threads the real
   memory limit: in-bounds returns the value (a 0 limit would always-trap),
   OOB traps.

Trap classification is STRICT to stay non-vacuous: only `brk`
(UC_ERR_EXCEPTION) counts as a WASM trap. A returned value or an
unmapped-memory fault (what the unchecked pre-fix code produces for -1)
counts as the miscompile it is.

Runs on any host (unicorn emulates A64). Needs wasmtime + unicorn +
pyelftools:
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_bounds_865_differential.py
"""

import hashlib
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_ERR_EXCEPTION, UC_MODE_ARM, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
    UC_ARM64_REG_X28,
)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

WAT = """(module
  (memory 1)
  (func (export "ld")  (param i32) (result i32) (i32.load    (local.get 0)))
  (func (export "ld8") (param i32) (result i32) (i32.load8_u (local.get 0)))
  (func (export "ldo") (param i32) (result i32)
        (i32.load offset=65532 (local.get 0)))
  (func (export "st")  (param i32 i32)
        (i32.store (local.get 0) (local.get 1)))
)
"""

# gale's exact single-function repro module (#865).
WAT_SINGLE = """(module (memory 1)
  (func (export "f") (param i32) (result i32) (i32.load (local.get 0))))
"""

# unicorn address map. LINMEM is 64 KiB of guest memory; MAPPED extends past
# the limit and is POISONED so an unchecked OOB read visibly returns garbage
# (gale's "reads host memory" row) instead of a lucky zero.
CODE, STK, RET = 0x100000, 0x400000, 0x500000
LINMEM = 0x1000000
LIMIT = 0x10000  # (memory 1) = 64 KiB
MAPPED = 0x30000  # 192 KiB mapped: covers addr 100000 (0x186A0) with poison
POISON = 0xEE
M32 = (1 << 32) - 1

# gale's table + width/offset edges: (fn, args, kind) where kind is
# "value" (must equal wasmtime's value) or "trap" (wasmtime traps; synth
# must brk). The wasmtime side is EXECUTED, not assumed — a "trap" row
# aborts if wasmtime unexpectedly succeeds.
TABLE = [
    ("ld", [65532], "value"),  # last in-bounds word
    ("ld", [65536], "trap"),  # 1 byte past — gale row 2
    ("ld", [100000], "trap"),  # gale row 3
    ("ld", [0xFFFFFFFF], "trap"),  # gale row 4 (uxtw reaches +4GiB-1)
    ("ld", [65533], "trap"),  # width: 4-byte access straddles the limit
    ("ld", [0], "value"),
    ("ld8", [65535], "value"),  # width: last single in-bounds byte
    ("ld8", [65536], "trap"),
    ("ldo", [0], "value"),  # memarg offset: 65532..65535 in-bounds
    ("ldo", [4], "trap"),  # memarg offset: 65536.. straddles
    ("ldo", [0xFFFFFFFF], "trap"),  # offset + uxtw(-1) far past the limit
    ("st", [65532, 0x11223344], "value"),  # in-bounds write (checked below)
    ("st", [65536, 0xDEAD], "trap"),  # the arbitrary-write primitive
    ("st", [0xFFFFFFFF, 0xDEAD], "trap"),
]


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def compile_synth(wat_path, out, extra):
    return run([SYNTH, "compile", str(wat_path), "-o", out, "-b", "aarch64"] + extra)


def load_elf(elf):
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


def new_uc(code):
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_map(LINMEM, MAPPED)
    # Poison everything past the guest limit: an unchecked OOB read returns
    # 0xEEEEEEEE, never a false-negative zero.
    mu.mem_write(LINMEM + LIMIT, bytes([POISON]) * (MAPPED - LIMIT))
    mu.mem_write(CODE, code)
    return mu


def call(mu, base, faddr, args):
    """Returns ("value", v) | ("trap", None) | ("fault", errno).

    Only UC_ERR_EXCEPTION (the `brk` the bounds check emits) counts as a
    trap; an unmapped-access fault is the UNCHECKED dereference escaping
    (pre-fix behavior for addr -1) and is reported distinctly.
    """
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mu.reg_write(UC_ARM64_REG_X28, LINMEM)
    for reg, v in zip([UC_ARM64_REG_X0, UC_ARM64_REG_X1], args):
        mu.reg_write(reg, v & M32)
    try:
        mu.emu_start(CODE + (faddr - base), RET, count=4000)
    except UcError as e:
        if e.errno == UC_ERR_EXCEPTION:
            return ("trap", None)
        return ("fault", e.errno)
    return ("value", mu.reg_read(UC_ARM64_REG_W0) & M32)


def wasmtime_run(wat_text, fn, args):
    """Returns ("value", v) | ("trap", None) — fresh instance per call."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, wat_text)
    store = wasmtime.Store(engine)
    exports = wasmtime.Instance(store, module, []).exports(store)
    sargs = [a - (1 << 32) if a & (1 << 31) else a for a in args]
    try:
        r = exports[fn](store, *sargs)
    except Exception:
        return ("trap", None)
    return ("value", (r or 0) & M32)


def main():
    fails = 0

    def check(ok, msg):
        nonlocal fails
        if not ok:
            fails += 1
            print(f"BUG {msg}")
        else:
            print(f"ok  {msg}")

    tmp = Path(tempfile.mkdtemp(prefix="a64_bounds_865_"))
    wat = tmp / "mem.wat"
    wat.write_text(WAT)
    wat_single = tmp / "single.wat"
    wat_single.write_text(WAT_SINGLE)

    # --- 2a. mode surface: mask/mpu must HARD-ERROR on -b aarch64 ---
    for mode in ("mask", "mpu"):
        r = compile_synth(
            wat, str(tmp / f"m_{mode}.o"), ["--all-exports", "--safety-bounds", mode]
        )
        check(
            r.returncode != 0 and "#865" in (r.stderr + r.stdout),
            f"--safety-bounds {mode} hard-errors on aarch64 (was a silent no-op)",
        )

    # --- 2b. none / software / default must compile; none != software ---
    objs = {}
    for mode, extra in (
        ("none", ["--safety-bounds", "none"]),
        ("software", ["--safety-bounds", "software"]),
        ("default", []),
    ):
        out = str(tmp / f"m_{mode}.o")
        r = compile_synth(wat, out, ["--all-exports"] + extra)
        if r.returncode != 0:
            print(f"BUG compile ({mode}) failed: {r.stderr.strip()}")
            sys.exit(1)
        objs[mode] = hashlib.md5(Path(out).read_bytes()).hexdigest()
    check(
        objs["none"] != objs["software"],
        f"modes DIFFER: md5(none)={objs['none'][:12]} != "
        f"md5(software)={objs['software'][:12]} (gale's byte-identical symptom gone)",
    )
    check(
        objs["default"] == objs["software"],
        "flag-absent DEFAULT == software (the default enforces)",
    )

    # --- 1. gale's executed table on the DEFAULT-compiled module ---
    code, base, syms = load_elf(str(tmp / "m_default.o"))
    for fn, args, kind in TABLE:
        if fn not in syms:
            check(False, f"{fn}: symbol missing (declined?)")
            continue
        wt = (
            ("trap", None)
            if kind == "trap"
            else wasmtime_run(WAT, fn, args)
        )
        if kind == "trap":
            # never assume: confirm wasmtime REALLY traps this row
            wt_actual = wasmtime_run(WAT, fn, args)
            if wt_actual[0] != "trap":
                check(False, f"{fn}{args}: expected wasmtime trap, got {wt_actual}")
                continue
        got = call(new_uc(code), base, syms[fn], args)
        if fn == "st" and kind == "value":
            # a void in-bounds store: it must complete (no trap/fault) and
            # the round-trip below proves the write landed.
            check(got[0] == "value", f"st{args}: in-bounds store completes, got {got}")
            continue
        if kind == "value":
            check(
                got == wt,
                f"{fn}({args[0]:#x}): in-bounds value A64={got} wasmtime={wt}",
            )
        else:
            check(
                got[0] == "trap",
                f"{fn}({args[0]:#x}): OOB must brk-trap (wasmtime traps), A64={got}",
            )

    # in-bounds store→load round-trip on ONE instance (write really landed)
    mu = new_uc(code)
    call(mu, base, syms["st"], [65532, 0x11223344])
    got = call(mu, base, syms["ld"], [65532])
    check(
        got == ("value", 0x11223344),
        f"st;ld round-trip at 65532 = 0x11223344, got {got}",
    )

    # --- 2c. the `none` opt-out is real: 65536 reads the poison, no brk ---
    code_n, base_n, syms_n = load_elf(str(tmp / "m_none.o"))
    got = call(new_uc(code_n), base_n, syms_n["ld"], [65536])
    check(
        got == ("value", 0xEEEEEEEE),
        f"--safety-bounds none at 65536 reads unchecked host memory "
        f"(documented opt-out), got {got}",
    )

    # --- 3. gale's exact single-function command threads the REAL limit ---
    r = compile_synth(
        wat_single, str(tmp / "single.o"), ["-n", "f", "--relocatable"]
    )
    if r.returncode != 0:
        check(False, f"single-func compile failed: {r.stderr.strip()}")
    else:
        code_s, base_s, syms_s = load_elf(str(tmp / "single.o"))
        got = call(new_uc(code_s), base_s, syms_s["f"], [65532])
        check(
            got == ("value", 0),
            f"single-func ld(65532) in-bounds (limit=64Ki, not 0), got {got}",
        )
        for addr in (65536, 100000, 0xFFFFFFFF):
            got = call(new_uc(code_s), base_s, syms_s["f"], [addr])
            check(got[0] == "trap", f"single-func ld({addr:#x}) traps, got {got}")

    print(
        "\nRESULT:",
        "PASS — aarch64 --safety-bounds enforces (#865: OOB traps, modes differ)"
        if not fails
        else f"FAIL ({fails})",
    )
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
