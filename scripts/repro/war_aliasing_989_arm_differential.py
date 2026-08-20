#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 344
"""#989 — ARM: `local.set`/`local.tee` CLOBBERS an earlier `local.get` of the
same local still on the operand stack (WAR aliasing).

THE DEFECT. On ARM, `local.get $x` of a REGISTER-HOMED local (a param in
r0-r3, or a #390-promoted local in r4-r8) pushes the local's HOME REGISTER
onto the operand stack by reference — no copy. A later `local.set`/`local.tee`
of the SAME local writes that home register directly (`mov home, val`),
destroying the value the earlier `local.get` pushed. Every consumer downstream
reads the post-write value. No register pressure, no i64, no spill is needed —
it is a bare `local.get`/`local.set` pair:

    war_set(a) = old_x + new_x where x=a then x=100  — correct: a + 100
    0046: mov   r0, r0      ; local.set $x (local.get $a) -> x lives in r0
    0048: movw  r1, #0x64
    004c: mov   r0, r1      ; local.set $x = 100 — OVERWRITES the pushed old x
    004e: adds  r2, r0, r0  ; 100 + 100
    -> returns 200 for EVERY input.

RV32 has carried the guard since #472 (`snapshot_aliases` — its fixture's own
comment: "Without it these miscompile"). This differential is the ARM leg's
red-first evidence: it asserts the CORRECT values (wasmtime ground truth), so
it FAILS on the unfixed tree — 44 wrong vectors across 4 exports, measured —
and records the fix the moment the snapshot lands.

THE FIXTURES ARE THE EXISTING ONES. `rv32_local_promotion_472.wat` (war_set /
war_tee — promoted non-param locals) and `aarch64_param_homing_851.wat`
(get_set_get_param_no_alias / tee_param_no_alias — register-homed PARAMS,
where the incoming argument is never read at all). Both files carry many
NON-aliasing exports (accum, rbw, swap_two_params, param_write_if_else, ...);
those are the contrast population the fix must NOT disturb, so every all-i32
export of both modules is compared, not just the four wrong ones.

Both ARM lowering paths are run: `--relocatable` (the direct selector,
`select_with_stack`, where #989 lives) and the self-contained/optimized path,
so a fix that only moves one is visible.

Budgets are SYMMETRIC (wasmtime fuel / unicorn instruction count): a vector
that exhausts either side is skipped on both (`param_countdown_sum(-1)` is a
2^32-iteration counted loop). A unicorn fault where wasmtime returned within
budget is a FAILURE, never a skip.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/war_aliasing_989_arm_differential.py
"""
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

REPRO = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
TARGET = "cortex-m4f"

FIXTURES = [
    "rv32_local_promotion_472.wat",
    "aarch64_param_homing_851.wat",
]

CODE, LIN = 0x100000, 0x40000
RET_PAD = CODE + 0x38000
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000

WASMTIME_FUEL = 2_000_000
UNICORN_INSNS = 400_000

MEM_POISON = 0xDEADBEEF
REG_POISON = 0xFEEDFACE
CORE_ARGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
R_ARM_THM_CALL, R_ARM_THM_JUMP24 = 10, 30
M32 = 0xFFFFFFFF

# Boundary-heavy and the same for every export (sliced to its arity), so the
# population is a property of the corpus, not of per-export tuning. Includes
# the issue's own vectors (0, -5, 65535, 0x7FFFFFFF) — the pre-fix tree
# returns a CONSTANT (200 / 300 / 10 / 30) on every one of them.
ARG_TUPLES = [
    (0, 0, 0, 0),
    (1, 2, 3, 4),
    (7, 5, 3, 1),
    (-5, -7, -9, -11),
    (100, 100, 100, 100),
    (-1, 1, -1, 1),
    (1, -1, 1, -1),
    (0xFFFF, 0x10000, 3, 2),
    (0x7FFFFFFF, -1, 0x7FFFFFFF, -1),
    (-1, 0x7FFFFFFF, 1, 0),
    (0, -1, 0, -1),
    (42, 13, 7, 99),
]

# Floor on vectors actually COMPARED (not merely entered): a run that skipped
# everything on budget grounds would still clear an entry count. Measured on
# this corpus: 15 all-i32 exports x 12 vectors x 2 legs = 360, minus the 20
# genuine budget skips (the 2^32-iteration countdown vectors on
# param_countdown_sum / cond_write_param_loop). Steady-state of the FIXED
# tree; the unfixed tree compares 335 (its WAR codegen pushes 5 more vectors
# over the symmetric budget) and fails on 110 mismatches long before this
# floor matters.
MIN_COMPARED = 340

emulations = 0


def die(msg):
    print(f"#989 ARM WAR ORACLE: FAIL — {msg}")
    sys.exit(1)


def compile_fixture(wat, out, relocatable):
    cmd = [SYNTH, "compile", str(wat), "--target", TARGET, "--all-exports", "-o", out]
    if relocatable:
        cmd.append("--relocatable")
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        die(f"synth compile failed ({' '.join(cmd)}):\n{p.stdout}\n{p.stderr}")
    return out


def encode_thm_bl(pc_at_reloc, target):
    """Re-encode a Thumb-2 BL, exactly as `ld` resolves R_ARM_THM_CALL."""
    off = (target - (pc_at_reloc + 4)) & 0x01FFFFFF
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    imm10, imm11 = (off >> 12) & 0x3FF, (off >> 1) & 0x7FF
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return 0xF000 | (s << 10) | imm10, 0xD000 | (j1 << 13) | (j2 << 11) | imm11


def load(path):
    """(symbols, .text with in-module branch relocations applied, base_vaddr)."""
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
        sec = e.get_section_by_name(".text")
        if sec is None:
            die("no .text section in the compiled object")
        base = sec["sh_addr"]
        text = bytearray(sec.data())
        for rel in e.iter_sections():
            if rel["sh_type"] not in ("SHT_REL", "SHT_RELA"):
                continue
            for r in rel.iter_relocations():
                t = r["r_info_type"]
                name = symtab.get_symbol(r["r_info_sym"]).name
                if t not in (R_ARM_THM_CALL, R_ARM_THM_JUMP24):
                    die(f"unexpected reloc type {t} against {name!r}")
                if name not in syms:
                    die(f"reloc names {name!r}, not a defined symbol")
                off = r["r_offset"]
                hw1, hw2 = encode_thm_bl(CODE + off, CODE + ((syms[name] - base) & ~1))
                struct.pack_into("<HH", text, off, hw1, hw2)
    return syms, bytes(text), base


def run(syms, text, base, name, args):
    """Execute one export under unicorn with the sub-SP stack POISONED."""
    global emulations
    if name not in syms:
        return None, f"symbol {name} missing from .symtab"
    addr = (syms[name] - base) & ~1
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x40000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_write(CODE, text)
    # Poison every word the callee's frame can occupy: a read of an
    # uninitialised slot is then legible instead of reading as a benign 0.
    mu.mem_write(STACK_BASE, struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    mu.reg_write(UC_ARM_REG_SP, SP0)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    for i in range(4):
        mu.reg_write(CORE_ARGS[i], (args[i] & M32) if i < len(args) else REG_POISON)
    mu.reg_write(UC_ARM_REG_LR, RET_PAD | 1)
    emulations += 1
    try:
        mu.emu_start((CODE + addr) | 1, RET_PAD, count=UNICORN_INSNS)
    except UcError as ex:
        return None, str(ex)
    if mu.reg_read(UC_ARM_REG_PC) & ~1 != RET_PAD & ~1:
        return None, "BUDGET"  # not a fault: the instruction budget ran out
    return mu.reg_read(UC_ARM_REG_R0) & M32, ""


def usable_exports(module):
    """[(name, arity)] for exports with an all-i32 <=4-param, i32 signature."""
    out = []
    for exp in module.exports:
        ty = exp.type
        if not isinstance(ty, wasmtime.FuncType):
            continue
        params = [str(p) for p in ty.params]
        results = [str(r) for r in ty.results]
        if len(params) <= 4 and all(p == "i32" for p in params) and results == ["i32"]:
            out.append((exp.name, len(params)))
    return out


def leg(engine, module, obj, label):
    """Run the whole matrix against one compiled object. (checks, fails, skips)."""
    syms, text, base = load(obj)
    checks = fails = skips = 0
    for name, arity in usable_exports(module):
        for tup in ARG_TUPLES:
            args = list(tup[:arity])
            store = wasmtime.Store(engine)
            store.set_fuel(WASMTIME_FUEL)
            inst = wasmtime.Instance(store, module, [])
            try:
                want = inst.exports(store)[name](store, *args) & M32
            except Exception as exc:
                if "fuel" in str(exc).lower():
                    skips += 1  # reference over budget — skip both sides
                    continue
                die(f"wasmtime trapped on {name}{tuple(args)}: {exc} — this corpus "
                    f"has no trapping export, so the harness is broken")
            got, err = run(syms, text, base, name, [a & M32 for a in args])
            if err == "BUDGET":
                skips += 1
                continue
            checks += 1
            if got != want:
                fails += 1
                shown = f"{got}" if got is not None else f"ERR({err})"
                print(f"BUG [{label}] {name}{tuple(args)}: want={want} got={shown}")
    return checks, fails, skips


def main():
    cfg = wasmtime.Config()
    cfg.consume_fuel = True
    engine = wasmtime.Engine(cfg)

    total_checks = total_fails = total_skips = 0
    with tempfile.TemporaryDirectory() as td:
        for fixture in FIXTURES:
            wat = REPRO / fixture
            module = wasmtime.Module(engine, wasmtime.wat2wasm(wat.read_text()))
            for label, reloc in (("relocatable", True), ("self-contained", False)):
                obj = compile_fixture(wat, os.path.join(td, f"{wat.stem}_{reloc}.o"), reloc)
                c, f, s = leg(engine, module, obj, f"{fixture}:{label}")
                print(f"[{fixture}:{label}] {c - f}/{c} vectors match wasmtime "
                      f"({s} over-budget skips)")
                total_checks += c
                total_fails += f
                total_skips += s

    if total_checks < MIN_COMPARED:
        print(f"FAIL floor: only {total_checks} vectors compared, floor {MIN_COMPARED} "
              f"— the differential lost its population, which is a coverage "
              f"regression, not a pass")
        total_fails += 1

    print(f"\n#989 CHECKS={total_checks - total_fails}/{total_checks} "
          f"(emulations={emulations}, skips={total_skips})")
    if total_fails:
        print("#989 ARM WAR-aliasing ORACLE: FAIL")
    else:
        print("#989 ARM WAR-aliasing ORACLE: PASS")
    sys.exit(1 if total_fails else 0)


if __name__ == "__main__":
    main()
