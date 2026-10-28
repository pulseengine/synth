#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 13680
"""#1594 (RQ-89-FLOATZERO) — EXECUTION-validate the wasm-mandated ZERO initial
value of a float (f32/f64) local that may be read before it is written.

WebAssembly zero-initialises every non-parameter local. synth's ARM selector
births a float local's home — a pinned VFP register on the base rung, or a
permanent frame slot on the #1069 `vfp-frame-locals` rung — at its FIRST
`local.set` in op order. When that write sits on one `if` arm, is skipped by
a `br_if`, or precedes a loop read only on some path, the read at the join
observed whatever the register/slot held before the birth: a temp's leftover
(register home) or stack garbage (frame home). Silent wrong value, rc=0.

This oracle compiles the two fixtures (`float_local_zero_init_1594.wat`,
f32; `..._f64.wat`, f64 — both GENERATED, shapes documented in their
headers) and runs every export under unicorn against wasmtime:

  1. COMPILE — every export reaches the object (no "skipping"), on
     cortex-m4f (--relocatable AND self-contained) and cortex-m7
     (--relocatable) for f32; cortex-m7dp (--relocatable AND self-contained)
     for f64. cortex-m4 has no FPU, so the f32 rows use m4f.
  1b. RUNG — from SYNTH_RECOVERY_STATS: every `r_*`/`c_*` export compiles
     on the `base` rung (REGISTER home), `s_cond` on `vfp-spill` (#881),
     `w_cond` (f32 only) on `vfp-wide-file` (#1267/#1439), every
     `p_*`/`m_*` export on `vfp-frame-locals` (FRAME home possible; `m_multi` has more
     read-before-write probes than the S7/D3 register-home cap, so some are
     frame-homed from entry). A ladder change that moves a shape off its rung
     would silently drop that home's coverage, so it fails here instead.
  2. EXECUTE bit-identically to wasmtime (NaN==NaN, WASM Core §4.3.3) in
     THREE machine states per vector:
       zz — zeroed stack, zeroed core+VFP registers;
       gz — GARBAGE stack (0x41414141 / 0x7FC00001 NaN / seeded random),
            zeroed registers — the state that exposes the FRAME home;
       zg — zeroed stack, GARBAGE core+VFP registers — exposes the
            REGISTER home's pre-birth contents.
     A zeroed-only oracle is BLIND to the frame-home half (it reads 0 by
     accident), which is why #1069's zeroed-stack oracle never saw this.
     This oracle SUBSUMES a one-branch float shape in the #1069 population
     (vfp_local_pressure_1069): every `p_*`/`m_*` row is a #1069
     frame-rung function (asserted by gate 1b) with a one-path write, and
     it runs the garbage-stack state that oracle does not — so no shape was
     added there.

Red-first (measured on origin/main d4c0b232, the pre-fix selector): the
read-before-write-in-op-order shapes (`*_first`, `*_loop`) DECLINE there
(GI-FPU-002 "expected an f32 operand"), so gate 1 fails; with those
excluded (a scratch variant tolerating the declines), every other shape
returns wrong values in gz and/or zg — 1362 of 10080 emulations wrong.
Fixed binary: 13680 of 13680 bit-identical.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python scripts/repro/float_local_zero_init_1594_differential.py
"""

import os
import random
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as A

HERE = Path(__file__).parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
FIXTURES = {
    "f32": HERE / "float_local_zero_init_1594.wat",
    "f64": HERE / "float_local_zero_init_1594_f64.wat",
}
# (fixture type, target, relocatable)
CONFIGS = [
    ("f32", "cortex-m4f", True),
    ("f32", "cortex-m4f", False),
    ("f32", "cortex-m7", True),
    ("f64", "cortex-m7dp", True),
    ("f64", "cortex-m7dp", False),
]
STK, STKSZ = 0x300000, 0x10000
SP0 = STK + STKSZ - 0x100
RET = 0x400000
MEM = 0x20000000
AV = [0.0, -0.0, 1.0, -1.0, 0.5, -3.14159265]
CV = [0, 1, 5, 200, 1023, -1]
MODES = {"zz": (False, False), "gz": (True, False), "zg": (False, True)}


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def exports_of(wat):
    return re.findall(r'\(export "([^"]+)"\)', wat.read_text())


def expected_rung(name):
    return {"r": "base", "c": "base", "s": "vfp-spill",
            "w": "vfp-wide-file"}.get(name[0], "vfp-frame-locals")


def compile_cfg(tmp, ty, target, reloc):
    out = str(Path(tmp) / f"{ty}_{target}_{'rel' if reloc else 'sc'}.o")
    cmd = [SYNTH, "compile", str(FIXTURES[ty]), "-o", out, "-t", target,
           "--all-exports"]
    if reloc:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True, env={**os.environ, "SYNTH_RECOVERY_STATS": "1"})
    log = r.stdout
    if r.returncode != 0 or "skipping function" in log:
        fail(f"{ty} {target} reloc={reloc}: compile failed / skipped a "
             f"function (rc={r.returncode}):\n{log[-3000:]}")
    rungs, cur = {}, None
    for line in log.splitlines():
        m = re.search(r"Compiling function '([^']+)'", line)
        if m:
            cur = m.group(1)
        m = re.search(r"\[recovery-stats\] rung=(\S+) result=ok", line)
        if m and cur is not None:
            rungs[cur] = m.group(1)
    for name in exports_of(FIXTURES[ty]):
        want = expected_rung(name)
        if rungs.get(name) != want:
            fail(f"{ty} {target} reloc={reloc}: '{name}' compiled on rung "
                 f"{rungs.get(name)!r}, expected {want!r} — the shape no "
                 f"longer exercises the home it is here to cover")
    return out


def load(path):
    ef = ELFFile(open(path, "rb"))
    t = ef.get_section_by_name(".text")
    syms = {}
    for s in ef.iter_sections():
        if s["sh_type"] == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for y in s.iter_symbols():
                if y.name and y["st_info"]["type"] == "STT_FUNC":
                    syms[y.name] = y["st_value"] & ~1
    return t.data(), t["sh_addr"], syms


def to_bits(ty, v):
    if ty == "f32":
        return struct.unpack("<I", struct.pack("<f", v))[0]
    return struct.unpack("<Q", struct.pack("<d", v))[0]


def is_nan(ty, b):
    if ty == "f32":
        return (b & 0x7F800000) == 0x7F800000 and (b & 0x7FFFFF) != 0
    return ((b & 0x7FF0000000000000) == 0x7FF0000000000000
            and (b & 0xFFFFFFFFFFFFF) != 0)


def emulate(ty, text, base, entry, a, c, gstack, gregs, rng, pat):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    uc.ctl_set_cpu_model(A.UC_CPU_ARM_MAX)
    lo = base & ~0xFFF
    uc.mem_map(lo, ((base - lo + len(text)) + 0x1FFF) & ~0xFFF)
    uc.mem_write(base, text)
    uc.mem_map(STK, STKSZ)
    uc.mem_map(RET, 0x1000)
    uc.mem_map(MEM, 0x10000)
    if gstack:
        if pat == 2:
            uc.mem_write(STK, rng.randbytes(STKSZ))
        else:
            word = [0x41414141, 0x7FC00001][pat]
            uc.mem_write(STK, struct.pack("<I", word) * (STKSZ // 4))
    uc.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)
    uc.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)
    uc.reg_write(A.UC_ARM_REG_FPSCR, 0)
    for i in range(32):
        uc.reg_write(getattr(A, f"UC_ARM_REG_S{i}"),
                     rng.getrandbits(32) if gregs else 0)
    for i in range(13):
        uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"),
                     rng.getrandbits(32) if gregs else 0)
    uc.reg_write(A.UC_ARM_REG_R11, MEM)
    uc.reg_write(A.UC_ARM_REG_R10, 0x10000)
    uc.reg_write(A.UC_ARM_REG_SP, SP0)
    uc.reg_write(A.UC_ARM_REG_LR, RET | 1)
    if ty == "f32":
        uc.reg_write(A.UC_ARM_REG_S0, to_bits(ty, a))
    else:
        uc.reg_write(A.UC_ARM_REG_D0, to_bits(ty, a))
    uc.reg_write(A.UC_ARM_REG_R0, c & 0xFFFFFFFF)
    try:
        uc.emu_start(entry | 1, RET, count=200000)
    except UcError as e:
        return ("trap", str(e))
    if uc.reg_read(A.UC_ARM_REG_PC) != RET:
        return ("hang", hex(uc.reg_read(A.UC_ARM_REG_PC)))
    if ty == "f32":
        return ("ok", uc.reg_read(A.UC_ARM_REG_S0) & 0xFFFFFFFF)
    return ("ok", uc.reg_read(A.UC_ARM_REG_D0) & ((1 << 64) - 1))


def main():
    eng = wasmtime.Engine()
    # Keyed by the argument's BIT pattern: 0.0 == -0.0 (and they hash alike)
    # in Python, so a float key would silently merge the two sign cases.
    ref = {}
    for ty, wat in FIXTURES.items():
        mod = wasmtime.Module(eng, wasmtime.wat2wasm(wat.read_text()))
        for name in exports_of(wat):
            for a in AV:
                for c in CV:
                    st = wasmtime.Store(eng)
                    inst = wasmtime.Instance(st, mod, [])
                    ref[(ty, name, to_bits(ty, a), c)] = to_bits(ty, inst.exports(st)[name](st, a, c))
    rng = random.Random(0x1594)
    total = bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        for ty, target, reloc in CONFIGS:
            obj = compile_cfg(tmp, ty, target, reloc)
            text, base, syms = load(obj)
            label = f"{ty} {target} {'rel' if reloc else 'sc'}"
            for name in exports_of(FIXTURES[ty]):
                if name not in syms:
                    fail(f"{label}: export '{name}' has no symbol")
                row = []
                for m, (gs, gr) in MODES.items():
                    ok = n = 0
                    for a in AV:
                        for c in CV:
                            want = ref[(ty, name, to_bits(ty, a), c)]
                            for pat in ((0, 1, 2) if gs else (0,)):
                                got = emulate(ty, text, base, syms[name], a, c,
                                              gs, gr, rng, pat)
                                n += 1
                                good = got[0] == "ok" and (
                                    got[1] == want
                                    or (is_nan(ty, got[1]) and is_nan(ty, want)))
                                if good:
                                    ok += 1
                                elif bad < 12:
                                    print(f"  WRONG {label} {name} {m} a={a} c={c} "
                                          f"pat={pat}: want {want:#x} got {got}")
                                bad += 0 if good else 1
                    total += n
                    row.append(f"{m}:{ok}/{n}")
                print(f"{label:22s} {name:14s} " + "  ".join(row))
    if bad:
        fail(f"{bad} of {total} emulations differ from wasmtime — a float "
             f"local read before its write on some path did not observe 0.0 "
             f"(#1594)")
    print(f"PASS: {total} emulations bit-identical to wasmtime (f32+f64, "
          f"register + frame homes, zeroed/garbage stack and registers)")


if __name__ == "__main__":
    main()
