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
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, STK, RET = 0x100000, 0x900000, 0x300000
EXPORTS = ["large3", "small3", "neg", "mixed", "ctrl", "spill12"]
INPUTS = [5, 0, -3, 1000, -100000, 7]


def wasmtime_run(fn, arg):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, arg)


def compile_optimized(out, cse_on, relocatable=False):
    env = {"PATH": "/usr/bin:/bin"}
    if cse_on:
        env["SYNTH_CONST_CSE"] = "1"
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
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

    # --relocatable NO-REGRESSION GATE (#242). gale's gust_mix 90→92 B regression
    # was on `--relocatable`, which routes through `select_direct()` — there the
    # INLINE const cache never runs, so the post-hoc `apply_const_cse` acts ALONE.
    # This is the precise path of the bug; the optimized-path gate above does not
    # exercise it (inline aliasing dominates there). We compile the corpus on the
    # direct path flag-on vs flag-off and assert no function grows. NOTE: post-hoc
    # CSE is currently INERT on this corpus (the direct selector does not emit the
    # redundant same-value-in-two-registers shape these arithmetic fixtures would
    # need) — so this gate is, for now, a tripwire that will light up the moment a
    # fixture that DOES trigger it (e.g. gale's gust_mix Q8 clamp mixer) is added.
    print("\n--- per-function no-regression gate, --relocatable / direct path (#242) ---")
    roff, ron = "/tmp/const_cse_reloc_off.o", "/tmp/const_cse_reloc_on.o"
    compile_optimized(roff, cse_on=False, relocatable=True)
    compile_optimized(ron, cse_on=True, relocatable=True)
    _, _, _, roff_sizes = load(roff)
    _, _, _, ron_sizes = load(ron)
    rgrew, rfired = 0, 0
    for fn in sorted(set(roff_sizes) & set(ron_sizes)):
        o, n = roff_sizes[fn], ron_sizes[fn]
        if n > o:
            rgrew += 1
            print(f"REGRESS {fn}: {o} -> {n} B (+{n - o}) — const-CSE grew a function")
        elif n < o:
            rfired += 1
            print(f"OK      {fn}: {o} -> {n} B (-{o - n}) — CSE fired")
    if rfired == 0:
        print(f"(post-hoc CSE inert on this corpus — {len(roff_sizes)} fns, none changed)")
    fails += rgrew

    print("\n--- instruction-count delta, optimized path (information) ---")
    off_n, on_n = insn_count(off_code), insn_count(on_code)
    print(f".text Thumb instructions: off={off_n}  on={on_n}  "
          f"delta={off_n - on_n} ({'fewer with CSE' if on_n < off_n else 'no change'})")

    print("\nRESULT:", "PASS" if not fails
          else f"FAIL ({fails} issue(s): mismatches and/or function growth)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
