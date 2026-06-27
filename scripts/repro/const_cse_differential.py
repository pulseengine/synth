#!/usr/bin/env python3
"""VCR-RA const-CSE (#242) — EXECUTION-validate the optimized-path const cache.

The ARM path re-materializes a constant at every use: the same `i32.const N`
becomes a fresh `movw`/`movt` (or `mov`) each time. gale measured this on silicon
— flat_flight spends 61% of its const materializations on values already sitting
in a register. `SYNTH_CONST_CSE=1` removes the redundant materializations via the
post-hoc `liveness::apply_const_cse` pass (it also enables an inline const cache
on the optimized path; this harness, run without `--relocatable`, exercises both).

CSE-LAST + SIZE GUARD (#242). gale's v0.17.0 burndown found const-CSE GREW a tiny
`--relocatable` function (`gust_mix` 90→92 B): retargeting a use kept a constant
resident longer and defeated a *downstream* immediate-fold that would otherwise
have absorbed it. Two fixes, both validated here: (1) `apply_const_cse` now runs
LAST in the pass pipeline, after every immediate-fold, so foldable consts are
already gone before CSE looks; (2) it size-guards each segment — committing a
removal/retarget only when it does not grow the segment's estimated bytes (e.g. a
retarget that flips a 16-bit `ldr` to its 32-bit form is declined). The guard's
decline path is unit-tested non-vacuously in `liveness.rs`; the per-function gate
below is the end-to-end enforcement over real compiled functions.

This is byte-CHANGING codegen, so the flag ships DEFAULT-OFF (off ⇒ byte-identical,
the frozen gate proves it). This harness is the correctness + no-regression oracle
for the flag-ON path: it compiles `const_cse.wat` with `SYNTH_CONST_CSE=1`, runs
each export under unicorn (UC_ARCH_ARM / Thumb), and asserts the returned value is
bit-identical to wasmtime ground truth across a spread of inputs (including
negatives and zero), THEN asserts no function grew flag-on vs flag-off. Covered
shapes (see the .wat header): large/small/negative/mixed consts, reuse ACROSS an
if/else (cache must reset), and a 12-live-local function that forces real spills.

It also runs a DIRECT-PATH (`--relocatable`) gate on `const_cse_direct.wat` —
the path gale's gust_mix regression lived on, where only the post-hoc pass
runs — asserting CSE actually fires there, stays bit-identical to wasmtime,
and never grows a function (non-vacuous: fails if the fixture stops firing).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/const_cse_differential.py
Exits nonzero on any value mismatch OR any function that grew under const-CSE.
"""
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("const_cse.wat")
# Direct-path (`--relocatable`) trigger fixtures — shapes that make the DIRECT
# selector emit the redundant const materialization `apply_const_cse` dedups, so
# the direct-path gate actually exercises gale's path (single-param, reloc-free →
# runnable under unicorn). See its header.
WAT_DIRECT = Path(__file__).with_name("const_cse_direct.wat")
DIRECT_EXPORTS = ["r1", "r2", "rneg"]
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, STK, RET = 0x100000, 0x900000, 0x300000
EXPORTS = ["large3", "small3", "neg", "mixed", "ctrl", "spill12"]
INPUTS = [5, 0, -3, 1000, -100000, 7]


def wasmtime_run(fn, arg, wat=WAT):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(wat))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, arg)


def compile_optimized(out, cse_on, relocatable=False, wat=WAT):
    env = {"PATH": "/usr/bin:/bin"}
    if cse_on:
        env["SYNTH_CONST_CSE"] = "1"
    cmd = [SYNTH, "compile", str(wat), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed (cse_on={cse_on}, reloc={relocatable}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms, fsizes = {}, {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"]
                    if sy["st_info"]["type"] == "STT_FUNC":
                        fsizes[sy.name] = sy["st_size"]
    return code, base, syms, fsizes


def unicorn_run(code, base, faddr, arg):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, 0x20000000)
    mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    raw = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    return struct.unpack("<i", struct.pack("<I", raw))[0]


def insn_count(code):
    # Rough Thumb instruction count: a halfword whose top 5 bits are 0b11101..
    # 0b11111 starts a 32-bit instruction; otherwise it is a 16-bit instruction.
    n, i = 0, 0
    while i + 2 <= len(code):
        hw = code[i] | (code[i + 1] << 8)
        wide = (hw >> 11) >= 0b11101
        i += 4 if wide else 2
        n += 1
    return n


def main():
    off_elf, on_elf = "/tmp/const_cse_off.elf", "/tmp/const_cse_on.elf"
    compile_optimized(off_elf, cse_on=False)
    compile_optimized(on_elf, cse_on=True)
    off_code, off_base, off_syms, off_sizes = load(off_elf)
    on_code, on_base, on_syms, on_sizes = load(on_elf)

    fails = 0
    for fn in EXPORTS:
        faddr = on_syms.get(fn)
        if faddr is None:
            print(f"FAIL {fn}: symbol missing")
            fails += 1
            continue
        for arg in INPUTS:
            exp = wasmtime_run(fn, arg)
            got = unicorn_run(on_code, on_base, faddr, arg)
            ok = isinstance(got, int) and got == exp
            if not ok:
                fails += 1
            print(f"{'OK  ' if ok else 'FAIL'} {fn} cse-on({arg}) = {got} "
                  f"(wasmtime {exp})")

    # NO-REGRESSION GATE (#242): const-CSE must never GROW any function. This is
    # gale's explicit ask after the gust_mix 90→92 B regression — enforced by the
    # CSE-last reorder (foldable consts are already folded) plus the per-segment
    # size guard in apply_const_cse. The guard's decline path is proven
    # non-vacuously by the liveness unit tests; this is the end-to-end gate over
    # real compiled functions.
    print("\n--- per-function no-regression gate (#242) ---")
    grew = 0
    for fn in EXPORTS:
        o, n = off_sizes.get(fn), on_sizes.get(fn)
        if o is None or n is None:
            continue
        if n > o:
            grew += 1
            print(f"REGRESS {fn}: {o} -> {n} B (+{n - o}) — const-CSE grew a function")
        else:
            tag = f"-{o - n}" if n < o else "0"
            print(f"OK      {fn}: {o} -> {n} B ({tag})")
    fails += grew

    # --relocatable DIRECT-PATH GATE (#242) — the precise path of gale's gust_mix
    # 90→92 B regression. `--relocatable` routes through `select_direct()`, where
    # the INLINE const cache never runs, so the post-hoc `apply_const_cse` acts
    # ALONE; the optimized-path gate above does not exercise this (inline aliasing
    # dominates there). The main `const_cse.wat` corpus is INERT on this path (its
    # shapes don't make the direct selector emit the redundant same-value-in-two-
    # registers materialization apply_const_cse dedups), so it gave no positive
    # evidence. `const_cse_direct.wat` DOES trigger it. This gate is NON-VACUOUS:
    # it asserts (a) CSE actually fires on ≥1 function (else the gate has gone
    # blind — fail), (b) no function grows (the no-regression property on gale's
    # path), and (c) every result is bit-identical to wasmtime under unicorn
    # (correctness of post-hoc CSE on the direct selector's output).
    print("\n--- direct-path (--relocatable) gate, const_cse_direct.wat (#242) ---")
    doff, don = "/tmp/const_cse_direct_off.o", "/tmp/const_cse_direct_on.o"
    compile_optimized(doff, cse_on=False, relocatable=True, wat=WAT_DIRECT)
    compile_optimized(don, cse_on=True, relocatable=True, wat=WAT_DIRECT)
    d_off_code, d_off_base, _, d_off_sizes = load(doff)
    d_on_code, d_on_base, d_on_syms, d_on_sizes = load(don)
    dgrew, dfired = 0, 0
    for fn in DIRECT_EXPORTS:
        o, n = d_off_sizes.get(fn), d_on_sizes.get(fn)
        if o is None or n is None:
            continue
        if n > o:
            dgrew += 1
            print(f"REGRESS {fn}: {o} -> {n} B (+{n - o}) — const-CSE grew a function")
        elif n < o:
            dfired += 1
            print(f"OK      {fn}: {o} -> {n} B (-{o - n}) — CSE fired (direct path)")
        else:
            print(f"--      {fn}: {o} B (inert)")
    # correctness vs wasmtime on the CSE-on direct-path object (reloc-free → runs)
    for fn in DIRECT_EXPORTS:
        faddr = d_on_syms.get(fn)
        if faddr is None:
            continue
        for arg in INPUTS:
            exp = wasmtime_run(fn, arg, wat=WAT_DIRECT)
            got = unicorn_run(d_on_code, d_on_base, faddr, arg)
            if not (isinstance(got, int) and got == exp):
                fails += 1
                print(f"FAIL {fn} cse-on(direct)({arg}) = {got} (wasmtime {exp})")
    fails += dgrew
    if dfired == 0:
        # Non-vacuity guard: if no function shrank, the fixture no longer triggers
        # post-hoc CSE on the direct path — the gate has gone blind. Fail loudly so
        # it is fixed rather than silently passing.
        fails += 1
        print("FAIL: direct-path gate is VACUOUS — no function exercised post-hoc "
              "CSE (fixture no longer triggers it). Fix const_cse_direct.wat.")
    else:
        print(f"direct-path gate non-vacuous: CSE fired on {dfired} function(s), "
              f"all results match wasmtime, none grew")

    print("\n--- instruction-count delta, optimized path (information) ---")
    off_n, on_n = insn_count(off_code), insn_count(on_code)
    print(f".text Thumb instructions: off={off_n}  on={on_n}  "
          f"delta={off_n - on_n} ({'fewer with CSE' if on_n < off_n else 'no change'})")

    print("\nRESULT:", "PASS" if not fails
          else f"FAIL ({fails} issue(s): mismatches and/or function growth)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
