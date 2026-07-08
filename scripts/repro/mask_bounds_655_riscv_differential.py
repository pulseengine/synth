#!/usr/bin/env python3
"""#655 — RV32 mask/software bounds: EXECUTION-validate the effective-address fix.

The #651 class, RISC-V twin of ARM PR #654: `emit_bounds_check`'s Mask arm
masked the OPERAND, then the caller re-added the static offset in the access's
addressing mode — any non-zero offset escaped the bound. It also never clamped
a multi-byte access's FINAL byte, and i64 accesses carried NO guard at all
(Software and Mask alike).

The oracle is the mask-semantics MODEL (PR #654's contract):

    masked = min((operand + offset) & (size-1), size - access_size)

Every exported function of mask_bounds_655.wat runs under unicorn
(UC_ARCH_RISCV) with the 64 KiB linear memory holding a deterministic byte
pattern and 0xEE sentinel bytes ABOVE the window; loads must return the
model's value (an escape reads sentinel — mismatch), stores must land at the
model address and leave the sentinel region untouched. For in-bounds inputs
the model coincides with wasm semantics, so those rows double as exactness
guards. Software mode additionally must TRAP (ebreak) on any access whose
final byte is out of bounds — including i64 (the unguarded-on-main gap).

RED on pre-fix main (offset escape, halfword wrap, word overhang, i64 rows,
software-i64 no-trap, huge-offset compile), GREEN on the #655 branch.

Run (needs unicorn + pyelftools):
  /tmp/synthvenv/bin/python scripts/repro/mask_bounds_655_riscv_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys

from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/mask_bounds_655.wat"
WAT_HUGE = "scripts/repro/mask_bounds_655_hugeoff.wat"
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000
SIZE = 0x10000  # (memory 1) = 64 KiB
SENTINEL = 0xEE

# Deterministic, position-dependent linear-memory pattern. The (i >> 8) term
# breaks the natural period-256 aliasing of a pure affine byte pattern, so two
# distinct in-window addresses (bug vs model) can't read the same word.
PATTERN = bytes(((i * 131 + (i >> 8) * 17 + 7) & 0xFF) for i in range(SIZE))


def model(operand, offset, access):
    """PR #654's mask-semantics contract for the guarded start address."""
    return min((operand + offset) & (SIZE - 1), SIZE - access)


def le(mem, addr, n):
    return int.from_bytes(mem[addr : addr + n], "little")


def compile_elf(wat, out, mode):
    r = subprocess.run(
        [SYNTH, "compile", wat, "-o", out, "-b", "riscv", "-t", "rv32imac",
         "--all-exports", "--relocatable", "--safety-bounds", mode],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    return r


def syms_and_code(elf):
    """Symbol addresses from the ELF symtab (never disasm text — host-dep)."""
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    base = text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] - base
    return syms, text.data()


def run_rv(code, fa, args):
    """Run one export; return (a0, linear_memory_bytes) or ('ERR:…', mem)."""
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    # Linear memory: 64 KiB pattern window + 64 KiB sentinel ABOVE it, all
    # mapped — an escaping access must be DETECTED by value/byte checks, not
    # masked by an unmapped-page fault.
    mu.mem_map(LIN, 0x20000)
    mu.mem_write(LIN, PATTERN + bytes([SENTINEL]) * SIZE)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_RISCV_REG_SP, STK)
    mu.reg_write(UC_RISCV_REG_S11, LIN)  # s11 = __linear_memory_base
    for r, v in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1), args):
        mu.reg_write(r, v & 0xFFFFFFFF)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + fa, RET, count=5000)
    except UcError as e:
        return f"ERR:{e}", mu.mem_read(LIN, 0x20000)
    return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF, mu.mem_read(LIN, 0x20000)


# (export, args, access_size, wat_offset) — loads return the LE value at the
# model address. Rows marked RED miscompiled (escaped / read unguarded) on
# pre-fix main.
LOAD_CASES = [
    # RED: in-bound operand, offset 2044 escapes -> pre-fix read sentinel.
    ("load_off_esc", (0xFFFC,), 4, 2044),
    ("load_off_esc", (0xF000,), 4, 2044),   # fully in-bounds: exactness
    # RED: word overhang — start size-2 must clamp to size-4.
    ("load_word", (0xFFFE,), 4, 0),
    ("load_word", (0x1234,), 4, 0),          # in-bounds exactness
    # Exactness at the last byte (size-vs-size-1 pin).
    ("load8", (0xFFFF,), 1, 0),
    ("load8", (0x0000,), 1, 0),
    # RED: ea == size wraps to 0 under mask semantics.
    ("load16_off", (0xFF02,), 2, 254),
    ("load16_off", (0x0100,), 2, 254),       # in-bounds exactness
    # RED: i64 had NO guard — start size-4 must clamp to size-8.
    ("load_i64_lo", (0xFFFC,), 8, 0),
    ("load_i64_hi", (0xFFFC,), 8, 0),
    ("load_i64_lo", (0x2000,), 8, 0),         # in-bounds exactness
    ("load_i64_hi", (0x2000,), 8, 0),
]


def expected_load(func, operand, access, offset):
    m = model(operand, offset, access)
    if func == "load_i64_hi":
        return le(PATTERN, m + 4, 4)
    n = min(access, 4)
    return le(PATTERN, m, n)


def check_mask_loads(syms, code):
    fails = 0
    for func, args, access, offset in LOAD_CASES:
        got, _ = run_rv(code, syms[func], args)
        want = expected_load(func, args[0], access, offset)
        ok = got == want
        fails += 0 if ok else 1
        shown = f"0x{got:08x}" if isinstance(got, int) else got
        tag = "" if ok else "  <-- MISMATCH (escaped the bound?)"
        print(f"mask {func}{args}: got={shown} model=0x{want:08x}{tag}")
    return fails


def check_mask_stores(syms, code):
    fails = 0
    # RED: store with escaping offset — pre-fix wrote into the sentinel.
    for func, args, access, offset, val_bytes in [
        ("store_off_esc", (0xFFFC, 0xDEADBEEF), 4, 2044,
         (0xDEADBEEF).to_bytes(4, "little")),
        ("store_off_esc", (0x1000, 0xCAFEF00D), 4, 2044,
         (0xCAFEF00D).to_bytes(4, "little")),
        # RED: i64 store, start size-4 -> clamp to size-8; value = v|v<<32.
        ("store_i64", (0xFFFC, 0x0BADF00D), 8, 0,
         (0x0BADF00D).to_bytes(4, "little") * 2),
    ]:
        res, mem = run_rv(code, syms[func], args)
        if isinstance(res, str):
            print(f"mask {func}{args}: {res}  <-- TRAPPED (mask must not trap)")
            fails += 1
            continue
        m = model(args[0], offset, access)
        landed = bytes(mem[m : m + access]) == val_bytes
        sentinel_ok = all(b == SENTINEL for b in mem[SIZE : 2 * SIZE])
        ok = landed and sentinel_ok
        fails += 0 if ok else 1
        why = "" if ok else (
            "  <-- ESCAPED: wrote outside the window" if not sentinel_ok
            else f"  <-- value not at model addr 0x{m:04x}"
        )
        print(f"mask {func}{args}: model_addr=0x{m:04x} landed={landed} "
              f"sentinel_intact={sentinel_ok}{why}")
    return fails


def check_software(syms, code):
    """Software mode: OOB final byte must TRAP — including i64 (the gap)."""
    fails = 0
    cases = [
        # (func, args, must_trap)
        ("load_i64_lo", (0xFFFC,), True),   # RED: i64 was unguarded
        ("store_i64", (0xFFFC, 0x11223344), True),
        ("load_word", (0xFFFE,), True),      # i32 guard regression pin
        ("load_off_esc", (0xFFFC,), True),
        ("load_word", (0x1234,), False),     # in-bounds must NOT trap
        ("load_i64_lo", (0x2000,), False),
        ("load8", (0xFFFF,), False),
    ]
    for func, args, must_trap in cases:
        got, _ = run_rv(code, syms[func], args)
        trapped = isinstance(got, str)
        ok = trapped == must_trap
        fails += 0 if ok else 1
        tag = "" if ok else (
            "  <-- NO TRAP (unguarded access escaped)" if must_trap
            else "  <-- SPURIOUS TRAP on an in-bounds access"
        )
        shown = got if trapped else f"0x{got:08x}"
        print(f"software {func}{args}: {shown} "
              f"(want {'trap' if must_trap else 'value'}){tag}")
    return fails


def check_huge_offset():
    """Mask mode folds arbitrary 32-bit offsets (u33-sound) — must compile
    and match the model; pre-fix synth rejects it in offset_to_imm."""
    elf = "/tmp/mask_bounds_655_huge.o"
    r = compile_elf(WAT_HUGE, elf, "mask")
    if r.returncode != 0:
        print(f"mask hugeoff: COMPILE FAILED  <-- pre-fix offset_to_imm decline\n"
              f"  {r.stderr.strip().splitlines()[-1] if r.stderr else ''}")
        return 1
    syms, code = syms_and_code(elf)
    fails = 0
    for operand in (0, 0x1234, 0xFFFC):
        got, _ = run_rv(code, syms["load_off_huge"], (operand,))
        want = expected_load("load_off_huge", operand, 4, 0xFFFF0000)
        ok = got == want
        fails += 0 if ok else 1
        shown = f"0x{got:08x}" if isinstance(got, int) else got
        tag = "" if ok else "  <-- MISMATCH"
        print(f"mask load_off_huge({operand:#x}): got={shown} "
              f"model=0x{want:08x}{tag}")
    return fails


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — `cargo build --release -p synth-cli` first")

    fails = 0
    mask_elf, sw_elf = "/tmp/mask_bounds_655_mask.o", "/tmp/mask_bounds_655_sw.o"
    for elf, mode in ((mask_elf, "mask"), (sw_elf, "software")):
        r = compile_elf(WAT, elf, mode)
        if r.returncode != 0:
            sys.exit(f"compile failed ({mode}): {r.stderr}")

    syms, code = syms_and_code(mask_elf)
    missing = [f for f, *_ in LOAD_CASES if f not in syms]
    if missing:
        sys.exit(f"SYMBOL MISSING in mask build: {missing}")
    fails += check_mask_loads(syms, code)
    fails += check_mask_stores(syms, code)

    sw_syms, sw_code = syms_and_code(sw_elf)
    fails += check_software(sw_syms, sw_code)

    fails += check_huge_offset()

    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
