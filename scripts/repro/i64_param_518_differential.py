#!/usr/bin/env python3
"""#518 — CHARACTERIZE the i64-param binop miscompile on BOTH selectors.

This is the *oracle-first* artifact for issue #518 (epic #242, VCR-RA/VCR-SEL):
it reproduces and QUANTIFIES the defect against wasmtime ground truth before the
gated fix lands. It does NOT change codegen — it compiles the in-tree fixture
`i64_param_518.wat`, runs each export under unicorn (i64-aware: lo in R0, hi in
R1), and compares to wasmtime. It exercises BOTH lowering paths:

  * OPTIMIZED  (`synth compile ... --target cortex-m4`)  — the IR path.
  * DIRECT     (`... --relocatable`)                     — the shipped/relocatable
                                                           path (`select_with_stack`).

ROOT CAUSE (both paths, one omission — an i64 *param* is never classified i64):
  * Direct: `infer_i64_locals` learns i64-ness only from `LocalSet`/`LocalTee` of
    an i64 producer; a param that is only READ keeps `is_i64=false`. So
    `local.get 0` pushes `StackVal::Reg{is_i64:false}`, its implicit high register
    (R1 = `i64_pair_hi(R0)`) is NOT reserved on the vstack, the following
    `i64.const` is allocated INTO R1, and `i64.add` then reads `a_hi=R1` — already
    clobbered. Low half is correct; high half returns the const's low word.
  * Optimized: `I64Load`'s param-home guard (`num_params >= 2`/`>= 4`) confuses a
    *register* count with a *param* count — a single `(param i64)` has
    num_params==1, so it falls through to a fresh callee-saved pair (R4:R5) that
    was never homed from R0:R1. The param is dropped entirely.

EXPECTED while the bug is live: BOTH paths diverge from wasmtime on the i64-param
functions (t_add/t_sub/t_or, and the AAPCS even-aligned t_mixed); the i32 control
(t_i32) stays correct. This script EXITS 0 when that characterization holds (the
bug reproduces exactly as documented) and EXITS 1 if reality diverges from the
documented root cause — i.e. it is a stable characterization guard, not a CI red
gate. When the gated fix lands, flip EXPECT_MISCOMPILE→False: the same script
becomes the pass/fail correctness oracle (all paths must then match wasmtime).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/synthvenv/bin/python \
      scripts/repro/i64_param_518_differential.py
"""
import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("i64_param_518.wat")
# The DECLINE half — now fully LOWERED for every register-resident i64 param:
#   * d_past_r3 (i64 param past R3 = on the caller's stack) was the #503-i64 case.
#   * d_call (a REGISTER-resident i64 param in a frame-backing (has-call)
#     function) was the last #518 sub-case, lowered by #837: the frame-backing
#     param slot is now sized from the DECLARED AAPCS width, so the pair is homed
#     into the frame and reloaded after the call. It moved from DECLINE_SKIPPED
#     to the emitted+executes set. See framebacking_i64param_837_differential.py
#     for the fuller gale-shape (mmio import + in-module call) execution oracle.
# d_leaf is the control: a leaf i64 param IS emitted. DECLINE_SKIPPED is now
# EMPTY — there is no register-resident i64-param shape that loud-skips (the only
# remaining honest decline is the register-pair-exhaustion RETRY, which no static
# fixture triggers; it is asserted by name in the selector, not here).
DECLINE_WAT = Path(__file__).with_name("i64_param_518_decline.wat")
DECLINE_SKIPPED = []                              # nothing loud-skips anymore
DECLINE_EMITTED = ["d_leaf", "d_past_r3", "d_call"]  # emitted + execute correctly
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET, R11 = 0x100000, 0x900000, 0x300000, 0x20000000

# The #518 fix is LANDED: the leaf register-resident i64-param cases are lowered
# correctly on both paths; the two unsupported sub-cases are declined loudly. So
# this is now the CORRECTNESS gate (every run must match wasmtime), not the
# pre-fix characterization. (Set True only to re-demonstrate the original bug on
# a pre-fix build.)
EXPECT_MISCOMPILE = False

# (export, arg-list, signature) — args/sig drive AAPCS-correct placement so the
# harness matches the TRUE calling convention, not synth's buggy mapping.
#   sig "i64"      -> one i64 param in R0:R1
#   sig "i32,i64"  -> i32 in R0, i64 EVEN-ALIGNED in R2:R3 (R1 skipped)
#   sig "i32"      -> one i32 param in R0
CASES = [
    ("t_add", [(7,)], "i64"),
    ("t_add", [(0xFFFFFFFF,)], "i64"),
    ("t_add", [(0x1_0000_0000,)], "i64"),
    ("t_sub", [(100,)], "i64"),
    ("t_or", [(0x8,)], "i64"),
    ("t_mixed", [(3, 10)], "i32,i64"),
    # AAPCS i64-param register-assignment matrix — the even-aligned-pair vs
    # sequential-index distinction the fix's mapping logic must get right.
    ("t_ii_add", [(7, 5)], "i64,i64"),          # p0=R0:R1, p1=R2:R3
    ("t_ii_add", [(0xFFFFFFFF, 1)], "i64,i64"),
    ("t_i64_i32", [(10, 3)], "i64,i32"),        # p0=R0:R1, p1=R2
    ("t_snd_i64", [(100, 40)], "i64,i64"),      # reads only p1=R2:R3
    ("t_i32", [(7,)], "i32"),
]
# functions whose result is i64 (read R0:R1) vs i32 (read R0 only)
I64_RESULT = {"t_add", "t_sub", "t_or", "t_mixed",
              "t_ii_add", "t_i64_i32", "t_snd_i64"}
I64_PARAM_FNS = I64_RESULT


def wasmtime_run(fn, args):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, *args)


def compile_synth(out, relocatable):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed (reloc={relocatable}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


def place_args(mu, args, sig):
    """Write args into registers per TRUE AAPCS (even-aligned i64 pairs)."""
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
    nxt = 0
    flat = [a for tup in args for a in tup]
    types = sig.split(",")
    vi = 0
    for t in types:
        v = flat[vi]
        vi += 1
        if t == "i64":
            if nxt % 2:  # even-align: skip an odd register
                nxt += 1
            mu.reg_write(regs[nxt], v & 0xFFFFFFFF)
            mu.reg_write(regs[nxt + 1], (v >> 32) & 0xFFFFFFFF)
            nxt += 2
        else:  # i32
            mu.reg_write(regs[nxt], v & 0xFFFFFFFF)
            nxt += 1


def unicorn_run(code, base, faddr, args, sig, i64_result):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, R11)
    place_args(mu, args, sig)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    lo = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    if i64_result:
        hi = mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF
        return lo | (hi << 32)
    return lo


def run_path(label, relocatable):
    out = f"/tmp/i518_{'rel' if relocatable else 'opt'}.o"
    compile_synth(out, relocatable)
    code, base, syms = load(out)
    print(f"\n=== {label} path ===")
    divergences = 0
    control_ok = True
    for fn, args, sig in CASES:
        faddr = syms.get(fn)
        if faddr is None:
            print(f"  {fn}: SYMBOL MISSING")
            divergences += 1
            if fn not in I64_PARAM_FNS:
                control_ok = False
            continue
        exp = wasmtime_run(fn, args[0])
        got = unicorn_run(code, base, faddr, args, sig, fn in I64_RESULT)
        match = isinstance(got, int) and got == exp
        flag = "ok " if match else "BUG"
        if not match:
            divergences += 1
            if fn not in I64_PARAM_FNS:  # an i32-control regression is a real fail
                control_ok = False
        print(f"  [{flag}] {fn}{args[0]} -> {got}  (wasmtime {exp})"
              + ("" if match else "  [MISCOMPILE: off by hi/param]"))
    return divergences, control_ok


def check_decline_contract():
    """Every register-resident i64-param shape must now be EMITTED and execute
    correctly (d_leaf leaf, d_past_r3 stack-passed #503-i64, d_call frame-backed
    across a call #837). DECLINE_SKIPPED is empty — the only remaining honest
    decline (the register-pair-exhaustion retry) is asserted by name in the
    selector, not by a static fixture. Returns the number of failures."""
    out = "/tmp/i518_decline.o"
    cmd = [SYNTH, "compile", str(DECLINE_WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports", "--relocatable"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        print(f"FAIL: decline fixture failed to compile: {r.stderr}")
        return 1
    code, base, syms = load(out)
    print("\n=== decline contract (loud-skip, not silent miscompile) ===")
    fails = 0
    for fn in DECLINE_SKIPPED:
        warned = f"skipping function '{fn}'" in r.stderr
        absent = fn not in syms
        ok = warned and absent
        if not ok:
            fails += 1
        why = "" if ok else (
            "  [" + ", ".join(
                ([] if warned else ["no warning"])
                + ([] if absent else ["SILENTLY EMITTED — regression!"])
            ) + "]"
        )
        print(f"  [{'ok ' if ok else 'BUG'}] {fn}: loud-skipped{why}")
    # emitted set: present in the symtab AND correct under unicorn
    for fn in DECLINE_EMITTED:
        if fn not in syms:
            print(f"  [BUG] {fn}: expected emitted, but it was skipped")
            fails += 1
            continue
        if fn == "d_leaf":
            # d_leaf: (param i64)(result i64) i64.add(p,3); run with p=7 -> 10
            ok = got_i64_leaf(code, base, syms[fn], 7) == leaf_expect(7)
        elif fn == "d_call":
            # d_call (#837): (param i64)(result i64)
            # i64.add(p, i64.extend_i32_u(helper(7))); helper returns its arg, so
            # = p + 7. Register-resident i64 param FRAME-BACKED across the call:
            # the pair is homed into the frame and reloaded after the bl — the
            # exact case #518 declined and #837 lowered. Needs the bl $helper
            # (func_0) resolved so the call executes.
            p = 0x1_0000_0009
            ok = got_i64_dcall(out, base, syms[fn], p) == (
                (p + 7) & 0xFFFFFFFFFFFFFFFF)
        else:
            # d_past_r3 (#503-i64): (param i32 i32 i32 i64)(result i64)
            # i64.add(p3,1); p3 arrives on the caller's stack at entry SP.
            p3 = 0x1_0000_0005
            ok = got_i64_past_r3(code, base, syms[fn], p3) == (
                (p3 + 1) & 0xFFFFFFFFFFFFFFFF)
        print(f"  [{'ok ' if ok else 'BUG'}] {fn}: emitted + executes correctly")
        if not ok:
            fails += 1
    return fails


def leaf_expect(p):
    # d_leaf = (i64.add (local.get 0) (i64.const 3))
    return (p + 3) & 0xFFFFFFFFFFFFFFFF


def got_i64_past_r3(code, base, faddr, p3):
    """d_past_r3 (#503-i64): p0..p2 = i32 in R0..R2, p3 = i64 at [entry SP]."""
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, R11)
    mu.reg_write(UC_ARM_REG_R0, 11)
    mu.reg_write(UC_ARM_REG_R1, 22)
    mu.reg_write(UC_ARM_REG_R2, 33)
    mu.mem_write(STK, (p3 & 0xFFFFFFFFFFFFFFFF).to_bytes(8, "little"))
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return (mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF) | (
        (mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF) << 32)


def got_i64_leaf(code, base, faddr, arg):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, R11)
    mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, (arg >> 32) & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return (mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF) | (
        (mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF) << 32)


def got_i64_dcall(elf, base, faddr, arg):
    """d_call (#837): resolve the in-module `bl func_N` (helper) reloc so the call
    executes, then run the frame-backed i64-param function at CODE. `base` is the
    .text sh_addr; the image is loaded at CODE, so relocs resolve against CODE."""
    import struct
    f = ELFFile(open(elf, "rb"))
    text = bytearray(f.get_section_by_name(".text").data())
    st = next(s for s in f.iter_sections() if s.header.sh_type == "SHT_SYMTAB")
    fsyms = {s.name: s["st_value"] for s in st.iter_symbols()
             if s.name and s["st_info"]["type"] == "STT_FUNC"}
    relsec = f.get_section_by_name(".rel.text")
    if relsec is not None:
        for r in relsec.iter_relocations():
            if r["r_info_type"] != 10:  # THM_CALL only (all internal here)
                continue
            sym = st.get_symbol(r["r_info_sym"])
            off = r["r_offset"]
            S = (CODE + fsyms[sym.name]) & ~1
            P = CODE + off + 4
            disp = S - P
            imm = (disp >> 1) & 0x3FFFFF
            s = (imm >> 21) & 1
            i1 = (imm >> 20) & 1
            i2 = (imm >> 19) & 1
            j1 = (~i1 & 1) ^ s
            j2 = (~i2 & 1) ^ s
            imm10 = (imm >> 11) & 0x3FF
            imm11 = imm & 0x7FF
            hi = 0xF000 | (s << 10) | imm10
            lo = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
            struct.pack_into("<HH", text, off, hi, lo)
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, bytes(text))
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, R11)
    mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, (arg >> 32) & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return (mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF) | (
        (mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF) << 32)


def main():
    opt_div, opt_ctrl = run_path("OPTIMIZED (--target cortex-m4)", relocatable=False)
    rel_div, rel_ctrl = run_path("DIRECT (--relocatable)", relocatable=True)
    decline_fails = check_decline_contract()

    print("\n--- characterization verdict ---")
    # The i32 control must ALWAYS match; only i64-param fns are allowed to diverge
    # while the bug is live. So a "healthy" buggy state = both paths diverge on
    # >=1 i64-param fn AND neither breaks the i32 control.
    if EXPECT_MISCOMPILE:
        ok = opt_div > 0 and rel_div > 0 and opt_ctrl and rel_ctrl
        print(f"opt divergences={opt_div} (control_ok={opt_ctrl})  "
              f"direct divergences={rel_div} (control_ok={rel_ctrl})")
        if ok:
            print("RESULT: PASS — #518 reproduces on BOTH paths exactly as the "
                  "root-cause documents (i64 param dropped/high-half clobbered "
                  "across the full single/dual/even-aligned matrix; i32 control "
                  "correct). Oracle ready for the gated fix.")
            sys.exit(0)
        print("RESULT: FAIL — reality diverged from the documented #518 root "
              "cause (a path no longer miscompiles, or the i32 control broke). "
              "Re-examine before trusting the fix spec.")
        sys.exit(1)
    else:
        total = opt_div + rel_div + decline_fails
        if total == 0:
            print("RESULT: PASS — both paths match wasmtime on every leaf i64-param "
                  "function across the full AAPCS matrix, the #503-i64 stack-param "
                  "case (d_past_r3) is emitted and correct, AND the frame-backed "
                  "REGISTER i64 param across a call (d_call) is now emitted and "
                  "executes correctly (#837). #518 i64-param class complete for "
                  "every register-resident shape.")
            sys.exit(0)
        print(f"RESULT: FAIL — {opt_div + rel_div} value divergence(s) + "
              f"{decline_fails} decline-contract failure(s); #518 not fully fixed.")
        sys.exit(1)


if __name__ == "__main__":
    main()
