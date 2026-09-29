#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 60
"""RQ-76-FALCON (#1318) — EXECUTE a value-carrying branch at f32.

WHY THIS EXISTS. cpetig's `opt.wasm` declined six functions, each containing a
`block` with an f32 RESULT reached by a branch. The direct selector lands a
carried value in the target block's designated result register; that register is
a CORE register, so a carried f32 fell through to the INTEGER peek and the
compile refused with "invalid wasm or an unlowered float op reached the integer
path". The module is valid wasm and the ops were lowered — only the
carried-value path was missing, so the diagnostic blamed the reporter.

WHY COMPILING IS NOT THE EVIDENCE. The fix makes the edges and the join
rendezvous in a frame slot. A rendezvous that stores to one slot and reloads
from another, or reloads BEFORE the label so branch-in paths read an unwritten
slot, still COMPILES and returns a plausible float. v0.72 shipped two silent
miscompiles that were introduced inside the fix for a third, in this same
selector. So every shape is EXECUTED under unicorn on a Cortex-M4F and compared
BIT-EXACT against wasmtime.

-0.0 IS IN THE ARGUMENT SET DELIBERATELY. The cheap way to copy an f32 without
adding an instruction is an arithmetic identity — `VADD.F32 Sd, Sm, #0`. That is
NOT a copy: -0.0 + 0.0 is +0.0. A bit-exact comparison catches it; a `==`
comparison does not, because -0.0 == 0.0 in both Python and IEEE-754. The two
`_i32` exports are CONTROLS: they compiled before this change and must still
compile and still execute correctly, which is what makes "the type, not the
shape" a measurement rather than a claim.

RED before the fix: the four f32 exports do not compile at all, so the
emulation count cannot reach its floor. GREEN after -> exit 0.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python3 scripts/repro/carried_float_branch_1318_differential.py
"""
import os
import re
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # pragma: no cover - older unicorn
    UC_ARM_REG_C1_C0_2 = UC_ARM_REG_FPEXC = None

HERE = Path(__file__).resolve().parent
WAT = HERE / "carried_float_branch_1318.wat"
# `oracle_run.py` sets SYNTH_BIN; the sibling differentials read that first
# and fall back to SYNTH so a direct invocation still works.
SYNTH = os.environ.get("SYNTH_BIN") or os.environ.get("SYNTH", "./target/debug/synth")
MEMBASE = 0x20000000

# Finite spread + both signed zeros + an infinity. NaN is deliberately ABSENT:
# `f32.add` may return any NaN payload per the spec, so a bit-exact comparison
# on a NaN would pin non-normative behaviour and read as a defect when it is not.
F32_ARGS = (0.0, -0.0, 1.5, -3.75, 2.5, float("inf"))
I32_ARGS = (0, 1, 7, 0x7FFFFFFF, 0xFFFFFFFF, 42)
CONDS = (0, 1)

# (export, kind, arity) — kind is the RESULT class.
SHAPES = (
    ("brif_f32", "f32", 2),
    ("br_f32", "f32", 1),
    ("brif_f32_d1", "f32", 2),
    ("brtable_f32", "f32", 2),
    ("brif_i32", "i32", 2),
    ("br_i32", "i32", 1),
)


def expected_emulations():
    """DERIVE the floor from the shape table, never a written-out product.

    RQ-75-FLOORBIND (#1331) found `emulations >= 15` written out as "3 fixtures
    x 5 args", so a FOURTH fixture silently restored the skip it closed — the
    literal could not move with the corpus. The header below must stay a
    literal, because `oracle_wiring_check.py` reads it STATICALLY without
    importing this module; so the binding runs the other way, and the module
    REFUSES to run when the two disagree.
    """
    return sum(len(F32_ARGS if k == "f32" else I32_ARGS) * len(CONDS if a == 2 else (None,))
               for _, k, a in SHAPES)


def declared_floor():
    src = Path(__file__).read_text()
    m = re.search(r"^# ci-checks: emulations >= (\d+)$", src, re.M)
    if not m:
        sys.exit("REFUSE: no `# ci-checks: emulations >= N` header in this file")
    return int(m.group(1))


def check_floor_binding():
    want, got = expected_emulations(), declared_floor()
    if want != got:
        sys.exit(
            f"REFUSE: the declared floor is `emulations >= {got}` but the shape "
            f"table derives {want}. Update the header in the same commit that "
            f"changes SHAPES/F32_ARGS/I32_ARGS/CONDS — a stale literal is how a "
            f"grown corpus silently stops being tested (#1331)."
        )


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def _key(v, kind):
    """A hashable identity that distinguishes +0.0 from -0.0 (see `wasm_refs`)."""
    return f32_bits(v) if kind == "f32" else (v & 0xFFFFFFFF)


def compile_elf(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", "cortex-m7", "--relocatable", "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    return r.returncode == 0, (r.stderr + r.stdout)


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def new_uc(text, text_base):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    map_base = text_base & ~0xFFF
    size = ((len(text) + (text_base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(text_base, text)
    uc.mem_map(0x30000, 0x10000)
    uc.mem_map(MEMBASE, 0x10000)
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    return uc


def run(text, base, addr, *, s0=None, r0=None, r1=None):
    uc = new_uc(text, base)
    if s0 is not None:
        uc.reg_write(UC_ARM_REG_S0, s0)
    if r0 is not None:
        uc.reg_write(UC_ARM_REG_R0, r0 & 0xFFFFFFFF)
    if r1 is not None:
        uc.reg_write(UC_ARM_REG_R1, r1 & 0xFFFFFFFF)
    ret = 0x38000
    uc.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        uc.emu_start(addr | 1, ret & ~1, count=400)
    except UcError as e:
        pc = uc.reg_read(UC_ARM_REG_PC)
        return ("fault", f"{e} at pc={pc:#x}")
    return ("ok", uc)


def wasm_refs():
    """Reference answers from wasmtime, keyed (export, args) -> result bits."""
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    refs = {}
    for name, kind, arity in SHAPES:
        fn = inst.exports(store)[name]
        vals = F32_ARGS if kind == "f32" else I32_ARGS
        for v in vals:
            conds = CONDS if arity == 2 else (None,)
            for c in conds:
                args = [v] if c is None else [v, c]
                if kind == "i32":
                    args = [int(a) if isinstance(a, int) else a for a in args]
                    args[0] = struct.unpack("<i", struct.pack("<I", v & 0xFFFFFFFF))[0]
                out = fn(store, *args)
                bits = f32_bits(out) if kind == "f32" else (out & 0xFFFFFFFF)
                # KEY ON BITS, NOT THE VALUE. `0.0 == -0.0` in Python AND they
                # hash equal, so keying on the float collapses the two signed
                # zeros into one entry and the second reference overwrites the
                # first. The first version of this harness did exactly that and
                # reported five failures against a CORRECT compiler — the
                # signed-zero bug this oracle exists to catch, committed by the
                # oracle, in its own lookup table.
                refs[(name, _key(v, kind), c)] = bits
    return refs


def main():
    check_floor_binding()
    out = "/tmp/carried_float_branch_1318.o"
    ok, log = compile_elf(out)
    if not ok:
        print("COMPILE FAILED — the carried-f32 shapes are still declined:")
        for line in log.splitlines():
            if "skipping function" in line or "Error" in line:
                print("   ", line.strip()[:160])
        print("carried-float-branch: 0 emulation(s) — RED")
        return 1

    text, base, syms = load(out)
    refs = wasm_refs()
    emulations = 0
    failures = []
    for name, kind, arity in SHAPES:
        if name not in syms:
            failures.append(f"{name}: absent from the symtab (declined?)")
            continue
        addr = syms[name] & ~1
        vals = F32_ARGS if kind == "f32" else I32_ARGS
        for v in vals:
            conds = CONDS if arity == 2 else (None,)
            for c in conds:
                if kind == "f32":
                    st, uc = run(text, base, addr, s0=f32_bits(v),
                                 r0=(c if c is not None else None))
                else:
                    st, uc = run(text, base, addr, r0=v,
                                 r1=(c if c is not None else None))
                emulations += 1
                if st != "ok":
                    failures.append(f"{name}({v}, {c}): {uc}")
                    continue
                got = (uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF) if kind == "f32" \
                    else (uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF)
                want = refs[(name, _key(v, kind), c)]
                if got != want:
                    # Print BITS, not the float: -0.0 and 0.0 print identically
                    # and compare equal, which is the whole point of the case.
                    failures.append(
                        f"{name}({v!r}, cond={c}): got {got:#010x} "
                        f"want {want:#010x} (bit-exact vs wasmtime)"
                    )

    for f in failures:
        print("  FAIL", f)
    print(f"carried-float-branch: {emulations} emulation(s) executed, "
          f"{len(failures)} failure(s)")
    # The line CI greps. Printed by this script rather than inferred from an
    # exit code, so a harness that never ran the comparison cannot satisfy it.
    print("RESULT: PASS" if not failures and emulations >= declared_floor()
          else "RESULT: FAIL")
    if emulations < declared_floor():
        print(f"  VACUOUS: {emulations} emulations is below the declared floor "
              f"of {declared_floor()}")
        return 1
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
