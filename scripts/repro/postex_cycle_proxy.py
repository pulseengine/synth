#!/usr/bin/env python3
"""VCR-VER-001 post-exhaustion cycle proxy (#242) — the PR #659 gate table,
reproducible.

For each pressure fixture, compiles the default path twice (flag off = the
#496 decline to the direct selector; SYNTH_SPILL_ON_EXHAUST=1 = the #580
allocation-time Belady spill + the post-exhaustion cleanup extensions), runs
the differential vectors under unicorn, and reports the weighted cycle proxy:
dynamic instructions + data-memory accesses (first-order M4: LDR/STR ~ 2 cyc,
everything else ~ 1). Every run is execution-matched against wasmtime — a
result mismatch fails the script, so the measurement doubles as an oracle.

Run:
  SYNTH=target/debug/synth python scripts/repro/postex_cycle_proxy.py
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_HOOK_CODE,
    UC_HOOK_MEM_READ,
    UC_HOOK_MEM_WRITE,
    UC_MODE_THUMB,
    Uc,
)
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_SP,
)

HERE = Path(__file__).parent
SYNTH = os.environ.get("SYNTH", "target/debug/synth")

# (fixture, export, param regs, result kind, vectors)
FIXTURES = [
    (
        "spill_on_exhaust_242.wat",
        "hp",
        2,
        "i32",
        [
            (0, 0),
            (1, 2),
            (3000, 50),
            (0x7FFFFFFF, 1),
            (0xFFFFFFFF, 0x80000000),
            (12345, 0xDEADBEEF),
            (7, 3),
            (0x12345678, 0x9ABCDEF0),
        ],
    ),
    (
        "spill_rung_581.wat",
        "hp",
        2,
        "i32",
        [(1, 2), (0, 0), (7, 3), (0xFFFFFFFF, 1), (12345, 54321), (2, 1)],
    ),
    (
        "high_pressure_i32.wat",
        "high_pressure",
        2,
        "i32",
        [
            (0, 0),
            (1, 2),
            (3000, 50),
            (0x7FFFFFFF, 1),
            (0xFFFFFFFF, 0x80000000),
            (12345, 0xDEADBEEF),
        ],
    ),
    (
        "signed_div_const.wasm",
        "filter_axis_decide",
        3,
        "i32",
        [
            (1000, 100, 500),
            (0xFFFFF830, 5, 5),  # -2000
            (7, 3, 0),
            (0x80000000, 0, 0),
            (123456, 0xFFFFFCEB, 42),  # -789
        ],
    ),
    (
        "i64_pair_exhaust_587.wat",
        "hp64",
        2,
        "i64",
        [
            (0, 0),
            (1, 2),
            (3000, 50),
            (0x7FFFFFFF, 1),
            (0xFFFFFFFF, 0x80000000),
            (12345, 0xDEADBEEF),
            (7, 3),
            (0x12345678, 0x9ABCDEF0),
        ],
    ),
    (
        "i64_spill_pool_587.wat",
        "hp20",
        1,
        "i64",
        [(0,), (1,), (3000,), (0x7FFFFFFF,), (0xFFFFFFFF,), (12345,)],
    ),
]

CODE, STK = 0x10000, 0x90000
PARAM_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2]


def compile_fixture(src: Path, flag_on: bool) -> bytes:
    env = dict(os.environ)
    env.pop("SYNTH_SPILL_ON_EXHAUST", None)
    if flag_on:
        env["SYNTH_SPILL_ON_EXHAUST"] = "1"
    with tempfile.NamedTemporaryFile(suffix=".elf") as f:
        subprocess.run(
            [
                SYNTH,
                "compile",
                str(src),
                "-o",
                f.name,
                "--target",
                "cortex-m4",
                "--all-exports",
            ],
            check=True,
            capture_output=True,
            env=env,
        )
        return Path(f.name).read_bytes()


def measure(elf_bytes: bytes, export: str, nparams: int, kind: str, vectors):
    """(total proxy, total insns, total accesses); asserts wasmtime match."""
    import io

    e = ELFFile(io.BytesIO(elf_bytes))
    text_sec = e.get_section_by_name(".text")
    text = text_sec.data()
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}
    entry_off = (syms[export] & ~1) - text_sec["sh_addr"]

    total_insns = total_acc = 0
    for vec in vectors:
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x10000)
        mu.mem_write(CODE, text)
        mu.mem_map(STK, 0x10000)
        ret = CODE + 0xFF00
        mu.mem_write(ret, b"\x00\xbf\x00\xbf")
        counts = [0, 0]  # insns, data accesses
        mu.hook_add(UC_HOOK_CODE, lambda u, a, s, d: counts.__setitem__(0, counts[0] + 1))
        mu.hook_add(
            UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
            lambda u, t, a, s, v, d: counts.__setitem__(1, counts[1] + 1),
        )
        for r, v in zip(PARAM_REGS, vec):
            mu.reg_write(r, v)
        mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
        mu.reg_write(UC_ARM_REG_LR, ret | 1)
        mu.emu_start((CODE + entry_off) | 1, ret, timeout=5_000_000)
        got = mu.reg_read(UC_ARM_REG_R0)
        if kind == "i64":
            got |= mu.reg_read(UC_ARM_REG_R1) << 32
        yield_check(export, vec, got, kind)
        total_insns += counts[0]
        total_acc += counts[1]
    return total_insns + total_acc, total_insns, total_acc


_GT_CACHE = {}


def yield_check(export, vec, got, kind):
    src, gt_export = _GT_CACHE["src"], _GT_CACHE["export"]
    eng = wasmtime.Engine()
    mod = wasmtime.Module.from_file(eng, str(src))
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    fn = inst.exports(st)[gt_export]
    sargs = [a - (1 << 32) if a >= 1 << 31 else a for a in vec]
    exp = fn(st, *sargs)
    exp &= (1 << 64) - 1 if kind == "i64" else 0xFFFFFFFF
    if got != exp:
        print(f"FAIL {export}{vec}: got {got:#x} expect {exp:#x}")
        sys.exit(1)


def main():
    print(f"{'fixture':30s} {'off (i+m)':>14s} {'on (i+m)':>14s} {'delta':>8s}")
    worst = []
    for name, export, nparams, kind, vectors in FIXTURES:
        src = HERE / name
        _GT_CACHE["src"], _GT_CACHE["export"] = src, export
        off = compile_fixture(src, False)
        on = compile_fixture(src, True)
        p_off, i_off, m_off = measure(off, export, nparams, kind, vectors)
        p_on, i_on, m_on = measure(on, export, nparams, kind, vectors)
        d = 100.0 * (p_on - p_off) / p_off
        worst.append((name, d))
        print(
            f"{name:30s} {p_off:5d} ({i_off}+{m_off}) {p_on:5d} ({i_on}+{m_on}) {d:+7.1f}%"
        )
    print("EXECUTION: all vectors matched wasmtime in both flag states")
    return 0


if __name__ == "__main__":
    sys.exit(main())
