#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 1120
"""#1069 (RQ-60-VFPPRESSURE increment 2) — EXECUTION-validate frame-homed
VFP locals on cortex-m7dp under falcon's exact flags
(`-t cortex-m7dp --relocatable`).

jess's discriminating measurement (fixture credit: jess): 60 simultaneously-
live f32 on the OPERAND STACK compile (#881 rescues them); 14 in HOMED LOCALS
do not — a home S-register is pinned for the function's extent and the #881
victim search skips homes. The fix frame-homes overflow locals from birth
(rung-only). This harness proves the emitted code is CORRECT, not merely
present:

  1. COMPILE — every export reaches an `nm -> T` symbol on
     `-t cortex-m7dp --relocatable` (live13 is the negative control);
  2. EXECUTE bit-identically to wasmtime (NaN==NaN per WASM Core §4.3.3)
     across representative values — a spill that reloads the wrong slot
     produces a plausible WRONG float, and every local's round-tripped value
     feeds the final product, so any slot mixup flips result bits:
       * live13 — negative control (base path, no rung);
       * live14/live16 — phase-1 S-file wall (attitude#tick / ekf#estimate);
       * live24 — grown-pool composition (>8 permanent slots);
       * live8d — the f64/D-file twin;
       * wide60/wsum60 — the vfp-wide-file rung (#1267) plus its pool-grow
         retry (#1439), the ONLY rung reaching them; gate 1b asserts that
         from SYNTH_RECOVERY_STATS so a ladder change that rescues them
         elsewhere cannot silently drop the rung's execution coverage.

RQ-89-GARBAGE1069 (#1613): every vector runs in three machine states -- zz
(zeroed stack and registers, the only state before), gz (GARBAGE stack:
0x41414141 / a NaN word / seeded random) and zg (GARBAGE core+VFP registers).
A zeroed-only run reads 0 from any uninitialised slot, which is the value wasm
mandates for a local, so it cannot see #1594 (a float local written on one
branch only, shipped v0.60-v0.88 on this very rung). The population is the 98
original rows plus 126 rows of a small one-branch-written fixture
(vfp_local_pressure_1069_zeroinit.wat: p_cond/p_brif f32, d_cond f64, gated
onto the vfp-frame-locals rung): 224 vectors, 1120 emulations.
Positive control: on a binary built from the commit before #1594's fix the zz
rows are all green and 80 of the 378 gz rows are wrong.

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld):
  SYNTH=/path/to/synth python scripts/repro/vfp_local_pressure_1069_differential.py
"""

import os
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, arm_const
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("vfp_local_pressure_1069.wat")
# RQ-89-GARBAGE1069: the one-branch-written float-local fixture (#1594 shape on
# the vfp-frame-locals rung). Exports take (a, c: i32).
WAT_ZI = Path(__file__).with_name("vfp_local_pressure_1069_zeroinit.wat")
ZI_F32 = ["p_cond", "p_brif"]
ZI_F64 = ["d_cond"]
ZI_EXPORTS = ZI_F32 + ZI_F64
CV = [0, 1, 200]  # the branch condition: probe unwritten / written / written
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

F32_EXPORTS = ["live13", "live14", "live16", "live24", "wide60", "wsum60"]
# #1439: the exports that must compile THROUGH the wide-file rung (gate 1b).
WIDE_FILE_EXPORTS = ["wide60", "wsum60"]
F64_EXPORTS = ["live8d"]
EXPORTS = F32_EXPORTS + F64_EXPORTS

# RQ-89-GARBAGE1069: every vector runs in THREE machine states, the naming
# float_local_zero_init_1594_differential.py uses:
#   zz -- zeroed stack, zeroed core+VFP registers (the ONLY state this oracle
#         ran before; blind to any read of an uninitialised frame slot or
#         register, which then reads 0 by accident -- #1594 shipped from v0.60
#         unseen by it);
#   gz -- GARBAGE stack (0x41414141 / a 0x7FC00001 NaN / seeded random),
#         zeroed registers -- exposes a FRAME home read before its write;
#   zg -- zeroed stack, GARBAGE core+VFP registers (seeded random) -- exposes
#         a REGISTER home's pre-birth contents.
# What is compared (bit-identical to wasmtime, NaN==NaN) is unchanged.
MODES = {"zz": (False, False), "gz": (True, False), "zg": (False, True)}
STACK_PATS = (0, 1, 2)  # 0x41414141, 0x7FC00001, seeded random
RNG = random.Random(0x1069)  # deterministic: same vectors every run


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_relocatable(tmp, wat=WAT, extra=()):
    obj = str(Path(tmp) / f"{wat.stem}.o")
    r = subprocess.run(
        [SYNTH, "compile", str(wat), "-o", obj,
         "-t", "cortex-m7dp", "--relocatable", *extra],
        # ONE stream, so each `[recovery-stats]` line (stderr) stays after the
        # `Compiling function` line (log) it belongs to (#1439 gate 1b).
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        env={**os.environ, "SYNTH_RECOVERY_STATS": "1"},
    )
    combined = r.stdout
    if r.returncode != 0:
        fail(f"compile failed:\n{combined}")
    if "skipping function" in combined:
        fail(f"a function was skipped (GI-FPU-002 regression):\n{combined}")
    return obj, combined


def rungs_by_function(log):
    """Map each compiled function to its `[recovery-stats]` lines (logging
    only — SYNTH_RECOVERY_STATS does not move a byte)."""
    out, cur = {}, None
    for line in log.splitlines():
        m = re.search(r"Compiling function '([^']+)'", line)
        if m:
            cur = m.group(1)
            out.setdefault(cur, [])
        elif "[recovery-stats]" in line and cur is not None:
            out[cur].append(line.strip())
    return out


def link(tmp, obj, entry="live13"):
    ld = shutil.which("arm-none-eabi-ld")
    if ld is None:
        fail("arm-none-eabi-ld not found")
    out = str(Path(tmp) / f"{Path(obj).stem}.elf")
    r = subprocess.run(
        [ld, "-e", entry, "-Ttext=0x0", obj, "-o", out],
        capture_output=True, text=True,
    )
    if r.returncode != 0 or r.stderr.strip():
        fail(f"link failed / diagnostics:\n{r.stderr}")
    return out


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def is_nan32(b):
    b &= 0xFFFFFFFF
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


def is_nan64(b):
    b &= (1 << 64) - 1
    return (b & 0x7FF0000000000000) == 0x7FF0000000000000 and (
        b & 0x000FFFFFFFFFFFFF) != 0


def f32_bits_eq(got, want):
    if is_nan32(got) and is_nan32(want):
        return True  # WASM Core §4.3.3: NaN payload non-deterministic
    return (got & 0xFFFFFFFF) == (want & 0xFFFFFFFF)


def f64_bits_eq(got, want):
    if is_nan64(got) and is_nan64(want):
        return True
    return (got & ((1 << 64) - 1)) == (want & ((1 << 64) - 1))


def new_uc(text, text_base, gs=False, gr=False, pat=0):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    try:
        from unicorn.arm_const import UC_CPU_ARM_MAX
        uc.ctl_set_cpu_model(UC_CPU_ARM_MAX)
    except (ImportError, AttributeError):
        pass
    map_base = text_base & ~0xFFF
    size = ((len(text) + (text_base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(text_base, text)
    uc.mem_map(0x30000, 0x10000)  # stack
    if gs:  # garbage stack: every frame slot starts non-zero
        if pat == 2:
            uc.mem_write(0x30000, RNG.randbytes(0x10000))
        else:
            word = (0x41414141, 0x7FC00001)[pat]
            uc.mem_write(0x30000, struct.pack("<I", word) * (0x10000 // 4))
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    if gr:  # garbage core + VFP registers (argument registers re-written after)
        for i in range(32):
            uc.reg_write(getattr(arm_const, f"UC_ARM_REG_S{i}"),
                         RNG.getrandbits(32))
        for i in range(13):
            uc.reg_write(getattr(arm_const, f"UC_ARM_REG_R{i}"),
                         RNG.getrandbits(32))
    return uc


def run_f32(text, base, addr, s0, c=None, gs=False, gr=False, pat=0):
    uc = new_uc(text, base, gs, gr, pat)
    uc.reg_write(UC_ARM_REG_S0, s0 & 0xFFFFFFFF)
    if c is not None:
        uc.reg_write(UC_ARM_REG_R0, c & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=5000)
    return uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF


def run_f64(text, base, addr, d0, c=None, gs=False, gr=False, pat=0):
    uc = new_uc(text, base, gs, gr, pat)
    uc.reg_write(UC_ARM_REG_D0, d0 & ((1 << 64) - 1))
    if c is not None:
        uc.reg_write(UC_ARM_REG_R0, c & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=5000)
    return uc.reg_read(UC_ARM_REG_D0) & ((1 << 64) - 1)


# Products of 14+ scaled copies overflow to inf fast for |a| >= ~1; keep a
# spread that exercises normals, denormal underflow, zeros, infinities and
# NaN through the spilled paths (each local's round-tripped value feeds the
# product, so a wrong-slot reload flips result bits).
VALS = [0.0, -0.0, 1.0, -1.0, 0.5, -0.25, 1.5, 0.001, -3.14159265,
        1e-30, -1e30, float("inf"), float("-inf"), float("nan")]

# RQ-81-WIDEFILE4 (#1439): BOTH SIGNS ARE LOAD-BEARING, and until v0.81 nothing
# said so. The wide-file sign error (#1439 — the number in this sentence read
# #1426 until v0.86, which is a DIFFERENT open defect: the frame-home spill-slot
# pool exhaustion on the reporter's last declining export. Two adjacent sentences
# in this block cited two issues for one subject, and the section header above has
# always had it right) shows as `got ^ want == 0x8000_0000`
# with magnitudes BIT-IDENTICAL, so exactly one factor's sign is wrong and only
# an `abs` or a `neg` can do that. For a NEGATIVE input the two are
# indistinguishable -- abs(-x) and neg(-x) both give +x -- so the positive rows
# are the discriminator: a `neg` would corrupt them too, an `abs` leaves them
# alone. v0.78 recorded the failing set as exactly the six NEGATIVE values and
# no positive one, and read that as identifying an ABS.
#
# REFUTED BY v0.89 (RQ-89-WIDEFILE11). The defect was neither an abs nor a neg:
# it was REGISTER ALIASING. The occupancy map widened to S0..S31 for the wide
# file, but the slot->register map still wrapped `% 16`, so the 17th grant came
# back as S0 (the param home) and every S16..S31 grant aliased a live
# caller-saved register. One factor of the product was therefore some OTHER
# value; the product saturates to +-inf/0, so only its sign survived. The
# non-saturating `wsum60` export failed 9 of 14 rows on that binary, POSITIVE
# inputs included. The sign-only signature was a property of this fixture, not
# of the defect. The span below stays asserted — it is still the row set the
# product exports are checked over.
import struct as _struct  # noqa: E402  (bit-exact row pinning, below)

_POS = [v for v in VALS if v == v and v > 0 or (v == 0 and str(v)[0] != "-")]
_NEG = [v for v in VALS if v == v and (v < 0 or str(v)[0] == "-")]
assert len(_POS) >= 4 and len(_NEG) >= 4, (
    f"VALS must span BOTH signs with at least 4 each -- it is the abs-vs-neg "
    f"discriminator for #1439, not decoration. Got {len(_POS)} positive and "
    f"{len(_NEG)} negative")
# AND THE ROWS, NOT ONLY THE COUNTS. (v0.81 round-1 cold review, finding 11.)
# The count assertion above says the comment's reason more narrowly than the
# comment claims: replacing every FINITE negative with an infinity or a denormal
# keeps 4-and-4 and still passes, while deleting exactly the rows v0.78's failing
# set is made of. Measured by the reviewer:
# `[0.0, -0.0, inf, -inf, 1e-30, -1e-30, 1e30, -1e30]` passed.
#
# v0.78 recorded the failing set as EXACTLY these six, so these six are the
# evidence and are pinned by VALUE. A future lane may add rows; it may not remove
# one of these without re-deriving the abs-vs-neg conclusion that rests on them.
_FAILING_SET_1439 = (-0.0, -1.0, -0.25, -3.14159265, -1e30, float("-inf"))
# COMPARE BY BIT PATTERN, not by `==`. (v0.81 round-2 cold review, finding 4.)
# The first version of this guard used `v not in VALS`, and `-0.0 == 0.0` is True
# in IEEE-754 — so membership was satisfied by `+0.0` and deleting `-0.0` left
# BOTH assertions passing. `-0.0` is the SIGN-BIT row: the one value in the set
# whose entire content is the sign, on a defect that is a sign error. The row most
# central to the conclusion was the only one not actually pinned.
_bits = {_struct.pack("<f", _v) for _v in VALS}
_missing = [v for v in _FAILING_SET_1439 if _struct.pack("<f", v) not in _bits]
assert not _missing, (
    f"VALS is missing {_missing} -- v0.78's recorded failing set for #1439 is "
    f"exactly {_FAILING_SET_1439}, and the abs-vs-neg conclusion is derived from "
    f"those rows failing while every POSITIVE row passed. Removing one deletes "
    f"the evidence rather than the test")

# RQ-82-PINBYVALUE (#1439): AND THE NON-FINITE ROWS, WHICH NOTHING PINNED AT ALL.
# The two guards above cover the sign span and v0.78's failing set; MEASURED, both
# stayed green when `float("nan")` was deleted from VALS. That row is in the
# fixture for a stated reason -- the header comment above says NaN exercises the
# spilled paths, because each local's round-tripped value feeds the product, so a
# wrong-slot reload flips result bits -- and it was protected by nothing.
#
# It is the SAME FAMILY as the `-0.0` escape and the OPPOSITE failure mode.
# `-0.0` was pinned VACUOUSLY TRUE, because `-0.0 == 0.0`, so membership was
# satisfied by the wrong row. NaN cannot be pinned by membership AT ALL, because
# `nan != nan` makes `nan in [nan]` False -- a membership guard over it would be
# vacuously FALSE and would red on a correct fixture. `struct.pack` settles both:
# it compares the BITS, where `-0.0` and `+0.0` differ and `nan` equals itself.
# The infinities ride along; they are cheap and they are the other rows whose
# content is not a magnitude.
#
# Deliberately a SEPARATE set from _FAILING_SET_1439, which means exactly "the six
# values v0.78 recorded as failing". Adding rows to that tuple would falsify its
# own name and the conclusion drawn from it.
# AND THE POSITIVE ROWS, FOR THE SAME REASON ONE TIER OVER. The comment above
# states the conclusion's shape: "the positive rows are the discriminator -- a
# `neg` would corrupt them too, an `abs` leaves them alone". So the conclusion
# rests on BOTH halves: the six negatives failing AND no positive one failing.
# The negative half is pinned by bits; the positive half was pinned only by
# `len(_POS) >= 4` against SEVEN present, so MEASURED, any single positive row
# could be deleted in silence -- deleting `0.0`, `1.0`, `0.5`, `1.5`, `0.001` or
# `1e-30` reddened nothing. Half an argument pinned is the asymmetry this lane
# exists to remove, not a smaller version of it.
_POSITIVE_SPAN_1439 = (0.0, 1.0, 0.5, 1.5, 0.001, 1e-30)
_NONFINITE_1069 = (float("inf"), float("-inf"), float("nan"))
_missing_nonfinite = [v for v in _NONFINITE_1069
                      if _struct.pack("<f", v) not in _bits]
assert not _missing_nonfinite, (
    f"VALS is missing {_missing_nonfinite} -- the non-finite rows exercise the "
    f"spilled reload paths this differential exists to check, and a membership "
    f"guard could never have pinned the NaN one. Re-derive the coverage claim "
    f"before removing a row rather than trimming to 'the interesting cases'")
_missing_positive = [v for v in _POSITIVE_SPAN_1439
                     if _struct.pack("<f", v) not in _bits]
assert not _missing_positive, (
    f"VALS is missing {_missing_positive} -- the POSITIVE rows are the "
    f"abs-vs-neg discriminator for #1439 (an `abs` leaves them alone, a `neg` "
    f"would corrupt them), so they are evidence exactly as the negative rows "
    f"are. `len(_POS) >= 4` does not pin them: seven are present, so the floor "
    f"permits deleting three in silence")


def main():
    tmp = tempfile.mkdtemp(prefix="vfp1069_")
    obj, log = compile_relocatable(tmp)

    # Gate 1b (#1439): the wide exports must be produced BY the wide-file rung
    # and its pool-grow retry. Without this, a ladder change that rescues them
    # through another rung would leave the executions below green while the
    # rung they exist to cover went unexecuted.
    stats = rungs_by_function(log)
    for name in WIDE_FILE_EXPORTS:
        lines = stats.get(name)
        if not lines:
            fail(f"{name}: no [recovery-stats] lines — the ladder never ran")
        if lines[-1] != "[recovery-stats] rung=vfp-wide-file result=ok":
            fail(f"{name}: not produced by the vfp-wide-file rung: {lines[-1]}")
        if not any("tried rung=vfp-wide-file+pool-grow(" in ln and ln.endswith("-> ok")
                   for ln in lines):
            fail(f"{name}: the wide-file pool-grow retry did not produce it:\n"
                 + "\n".join(lines))
    print(f"PASS: {len(WIDE_FILE_EXPORTS)} exports compiled through "
          "vfp-wide-file+pool-grow (the rung under test is the one reached)")

    # Gate 1: every export is an emitted T symbol (see the #850 note in
    # vfp_spill_881_differential.py — pyelftools, never host nm).
    with open(obj, "rb") as fh:
        ef = ELFFile(fh)
        symtab = next((s for s in ef.iter_sections()
                       if s["sh_type"] == "SHT_SYMTAB"), None)
        if symtab is None:
            fail("relocatable object has no SHT_SYMTAB section")
        tsyms = set()
        for sym in symtab.iter_symbols():
            if not sym.name or sym["st_info"]["bind"] != "STB_GLOBAL":
                continue
            shndx = sym["st_shndx"]
            if shndx in ("SHN_UNDEF", "SHN_ABS", "SHN_COMMON"):
                continue
            if ef.get_section(shndx)["sh_flags"] & 0x4:  # SHF_EXECINSTR
                tsyms.add(sym.name)
    missing = [e for e in EXPORTS if e not in tsyms]
    if missing:
        fail(f"exports missing from nm -> T: {missing}")
    print(f"PASS: all {len(EXPORTS)} exports emitted (nm -> T) under "
          "-t cortex-m7dp --relocatable")

    # Gate 2: execution, bit-exact vs wasmtime.
    elf = link(tmp, obj)
    text, base, syms = load(elf)
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    exp = inst.exports(store)

    checked = 0
    per_mode = {m: 0 for m in MODES}

    def sweep(kind, name, a, c, want, addr, txt, bs):
        """One vector in every machine state; returns emulations run."""
        n = 0
        run = run_f32 if kind == "f32" else run_f64
        eq = f32_bits_eq if kind == "f32" else f64_bits_eq
        w = 8 if kind == "f32" else 16
        for m, (gs, gr) in MODES.items():
            for pat in (STACK_PATS if gs else (0,)):
                got = run(txt, bs, addr, f32_bits(a) if kind == "f32"
                          else f64_bits(a), c, gs, gr, pat)
                if not eq(got, want):
                    fail(f"{name}({a}{'' if c is None else f', {c}'}) "
                         f"[{m} pat={pat}]: got {got:#0{w + 2}x}, "
                         f"want {want:#0{w + 2}x}")
                n += 1
                per_mode[m] += 1
        return n

    for name in F32_EXPORTS:
        for a in VALS:
            want = f32_bits(exp[name](store, a))
            checked += sweep("f32", name, a, None, want,
                             syms[name], text, base)
    for name in F64_EXPORTS:
        for a in VALS:
            want = f64_bits(exp[name](store, a))
            checked += sweep("f64", name, a, None, want,
                             syms[name], text, base)

    # RQ-89-GARBAGE1069: the one-branch-written float-local fixture.
    zobj, zlog = compile_relocatable(tmp, WAT_ZI, ("--all-exports",))
    zstats = rungs_by_function(zlog)
    for name in ZI_EXPORTS:
        lines = zstats.get(name)
        if not lines or lines[-1] != "[recovery-stats] rung=vfp-frame-locals result=ok":
            fail(f"{name}: not produced by the vfp-frame-locals rung "
                 f"({lines}) -- the zero-init fixture no longer exercises "
                 f"the frame home it is here to cover")
    print(f"PASS: {len(ZI_EXPORTS)} zero-init exports compiled on "
          "vfp-frame-locals")
    zelf = link(tmp, zobj, ZI_EXPORTS[0])
    ztext, zbase, zsyms = load(zelf)
    zmod = wasmtime.Module(eng, WAT_ZI.read_bytes())
    for name in ZI_EXPORTS:
        kind = "f32" if name in ZI_F32 else "f64"
        bits = f32_bits if kind == "f32" else f64_bits
        for a in VALS:
            for c in CV:
                zs = wasmtime.Store(eng)
                zi = wasmtime.Instance(zs, zmod, [])
                want = bits(zi.exports(zs)[name](zs, a, c))
                checked += sweep(kind, name, a, c, want,
                                 zsyms[name], ztext, zbase)

    print(f"PASS: {checked} emulations bit-identical to wasmtime "
          "(frame-homed VFP locals round-trip bit-exactly; zeroed/garbage "
          "stack and registers: "
          + ", ".join(f"{m}={n}" for m, n in per_mode.items()) + ")")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
