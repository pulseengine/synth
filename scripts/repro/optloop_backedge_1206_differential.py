#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 3200
"""#1206 (EST1206) — EXECUTION-validate do-while `br_if` back-edges on the
DEFAULT optimized Thumb-2 path.

The optimized path (`optimizer_bridge::ir_to_arm`) resolves every branch
displacement by summing `estimate_arm_byte_size`, a hand-written mirror of the
Thumb-2 encoder. When a loop condition's `SetCond` was allocated to R8 the
encoder emitted `ite; mov.w r8,#1; mov.w r8,#0; cmp.w r8,#0` (14 bytes) and
the estimator assumed 8 (`SetCond => 6`, `cmp => 2`), so the back-edge landed
6 bytes short — after the loop's increment — and any loop needing a second
iteration never terminated. Exit 0, no warning, on cortex-m3/m4/m4f/m7/m7dp.

This oracle compiles `optloop_backedge_1206.wat` self-contained (the default
image, `--target T --all-exports`) for the five Cortex-M targets and:

  1. PATH — asserts every export compiled on the OPTIMIZED path
     (`SYNTH_PATH_DEBUG`: "optimized (ir_to_arm ok)"). A shape that drifts
     to the direct selector would execute correctly for the wrong reason and
     silently stop testing the estimator; it fails here instead. A function
     the compile-time branch-landing check REFUSES ("skipping function")
     fails here too.
  2. EXECUTE every export under unicorn, entered at its ELF symbol, against
     wasmtime, over a fixed vector set, with an INSTRUCTION BUDGET: a hang
     is a FAIL with the stuck PC, never a CI timeout.

Shapes: #1206's own `countdown`; count-up with a const bound and with a param
bound (`do { i++ } while (i < n)`); count-down with a param bound and with a
const bound; a local initialised from a constant; `msize_loop` — a
`memory.size` in the loop body, a SECOND estimator drift class (LSR.W rd,
r10, #16 is 4 bytes, sized 2) that the #1206 audit found by census; and the
control `countdown_r7`, the same countdown whose SetCond lands in R7 (16-bit
forms) and was correct before the fix — if it fails, the harness is broken.

Red-first, measured on origin/main df847a16: 1595 of 3200 emulations hang —
7 of the 8 exports on every target; the `countdown_r7` control passes 400/400.
Green on the fix: 3200/3200. Potency, measured with planted mutants on the
fix: reverting the `SetCond` high-rd estimator arm makes the compile-time
landing check REFUSE 7 of 8 exports (gate 1 red); reverting the `MemorySize`
arm alone makes it refuse `msize_loop` (gate 1 red); reverting the `SetCond`
arm with the landing check disabled hangs 1420 of 3200 (gate 2 red). Other
fixed arms (e.g. the sub-word load/store rows) are not exercised by this
fixture; the exhaustive `estimator_encoder_agreement` test pins those.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python3 scripts/repro/optloop_backedge_1206_differential.py
"""

import os
import re
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
FIXTURE = HERE / "optloop_backedge_1206.wat"
TARGETS = ["cortex-m3", "cortex-m4", "cortex-m4f", "cortex-m7", "cortex-m7dp"]
CONTROL = "countdown_r7"
# One page: wasmtime's memory.size is 1; R10 carries the byte size on target.
MEM_BYTES = 0x10000
STK, STKSZ = 0x300000, 0x10000
SP0 = STK + STKSZ - 0x100
RET = 0x400000
BUDGET = 100_000
# (a, b): first two i32 params (a single-param export ignores b). Chosen so
# every export runs zero, one and many iterations and stays well inside the
# budget on a correct binary (a negative start would be ~4G iterations of
# `up_from_zero`, an unsigned count — a budget exhaustion, not a defect).
VECTORS = [(a, b) for a in (0, 1, 2, 5, 9, 10, 15, 37, 100, 200)
           for b in (0, 1, 3, 9, 10, 64, 100, 200)]


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def exports():
    return re.findall(r'\(export "([^"]+)"\)', FIXTURE.read_text())


def nparams(name):
    m = re.search(r'\(export "' + re.escape(name) + r'"\)\s*\(param ([^)]*)\)',
                  FIXTURE.read_text())
    return len(m.group(1).split()) if m else 0


def compile_target(tmp, target):
    out = str(Path(tmp) / f"{target}.elf")
    r = subprocess.run(
        [SYNTH, "compile", str(FIXTURE), "-o", out, "--target", target,
         "--all-exports"],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        env={**os.environ, "SYNTH_PATH_DEBUG": "1"})
    log = r.stdout
    if r.returncode != 0 or "skipping function" in log:
        fail(f"{target}: compile failed or skipped a function "
             f"(rc={r.returncode}):\n{log[-3000:]}")
    optimized = set(int(i) for i in re.findall(
        r"\[path-debug\] optimized \(ir_to_arm ok\) func=(\d+)", log))
    for idx, name in enumerate(exports()):
        if idx not in optimized:
            fail(f"{target}: '{name}' (func {idx}) did not compile on the "
                 f"optimized path — it no longer exercises the estimator")
    return out


def load(path):
    ef = ELFFile(open(path, "rb"))
    segs = [(s["p_vaddr"], s.data()) for s in ef.iter_segments()
            if s["p_type"] == "PT_LOAD" and s["p_filesz"] > 0]
    syms = {}
    for s in ef.iter_sections():
        if s["sh_type"] == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for y in s.iter_symbols():
                if y.name and y["st_info"]["type"] == "STT_FUNC":
                    syms[y.name] = y["st_value"] & ~1
    return segs, syms


def emulate(segs, entry, args):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    uc.ctl_set_cpu_model(A.UC_CPU_ARM_MAX)
    mapped = []
    for vaddr, data in segs:
        lo = vaddr & ~0xFFF
        hi = (vaddr + len(data) + 0xFFF) & ~0xFFF
        if not any(lo < h and hi > l for l, h in mapped):
            uc.mem_map(lo, hi - lo)
            mapped.append((lo, hi))
        uc.mem_write(vaddr, data)
    uc.mem_map(STK, STKSZ)
    uc.mem_map(RET, 0x1000)
    if not any(lo <= 0x20000000 < hi for lo, hi in mapped):
        uc.mem_map(0x20000000, 0x40000)
    uc.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)
    uc.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)
    uc.reg_write(A.UC_ARM_REG_R10, MEM_BYTES)
    uc.reg_write(A.UC_ARM_REG_R11, 0x20000000)
    uc.reg_write(A.UC_ARM_REG_SP, SP0)
    uc.reg_write(A.UC_ARM_REG_LR, RET | 1)
    for i, v in enumerate(args):
        uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), v & 0xFFFFFFFF)
    try:
        uc.emu_start(entry | 1, RET, count=BUDGET)
    except UcError as e:
        return ("trap", f"{e} pc={uc.reg_read(A.UC_ARM_REG_PC):#x}")
    pc = uc.reg_read(A.UC_ARM_REG_PC)
    if pc != RET:
        return ("hang", f"pc={pc:#x} after {BUDGET} instructions")
    return ("ok", uc.reg_read(A.UC_ARM_REG_R0) & 0xFFFFFFFF)


def main():
    names = exports()
    if CONTROL not in names or len(names) < 2:
        fail(f"fixture lost its exports or the {CONTROL} control: {names}")
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wasmtime.wat2wasm(FIXTURE.read_text()))
    ref = {}
    for name in names:
        n = nparams(name)
        for a, b in VECTORS:
            st = wasmtime.Store(eng)
            inst = wasmtime.Instance(st, mod, [])
            ref[(name, a, b)] = inst.exports(st)[name](st, *(a, b)[:n]) & 0xFFFFFFFF

    total = bad = 0
    control_bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        for target in TARGETS:
            segs, syms = load(compile_target(tmp, target))
            for name in names:
                if name not in syms:
                    fail(f"{target}: export '{name}' has no symbol")
                n = nparams(name)
                ok = hangs = 0
                for a, b in VECTORS:
                    want = ref[(name, a, b)]
                    got = emulate(segs, syms[name], (a, b)[:n])
                    total += 1
                    if got == ("ok", want):
                        ok += 1
                        continue
                    bad += 1
                    control_bad += name == CONTROL
                    hangs += got[0] == "hang"
                    if bad <= 12:
                        print(f"  WRONG {target} {name}({a}, {b}): "
                              f"want {want} got {got}")
                print(f"{target:12s} {name:14s} ok {ok}/{len(VECTORS)}"
                      + (f"  hang {hangs}" if hangs else ""))
    if control_bad:
        fail(f"the {CONTROL} control (R7 SetCond, correct before #1206) "
             f"failed {control_bad} time(s) — the harness is broken")
    if bad:
        fail(f"{bad} of {total} emulations differ from wasmtime or hang — "
             f"an optimized-path back-edge does not land on its loop head "
             f"(#1206)")
    print(f"PASS: {total} emulations match wasmtime ({len(names)} exports x "
          f"{len(VECTORS)} vectors x {len(TARGETS)} targets, budget {BUDGET})")


if __name__ == "__main__":
    main()
