#!/usr/bin/env python3
"""#503 (epic #242) — EXECUTION-validate the AAPCS stack-argument path for
functions with >8 scalar i32 params/args.

The arm backend used to SKIP (emit no code for) any function whose signature
needs the AAPCS stack-argument path beyond a conservative cap — `num_params > 8`
or a call passing `arg_count > 8`. gale hit this on the falcon flight component:
3 reachable helpers (10-param, 25-param, and a 64-bit case) were dropped from the
ELF. The incoming-param homing (`compute_local_layout` → `incoming_params`,
offset `frame_size+24+(k-4)*4`) and the outgoing store (`emit_stack_args`, offset
`(k-4)*4`) are both GENERIC in the index; #503 lifts the >8-scalar caps and leans
on the existing 12-bit `[sp,#imm]` guards. (The 64-bit stack-PARAM case is now
lowered too — width-aware NSAA homing, gated separately by
i64_stack_param_503_differential.py.)

This harness compiles via the SHIPPED direct path (`--relocatable`, what falcon
uses → `select_with_stack`), then runs each export under unicorn (UC_ARCH_ARM /
Thumb) with the AAPCS calling convention set up by hand:
  - args 0..3   → r0..r3
  - args 4..N   → pushed to the caller stack so that at entry `[sp,#0]`=arg4,
                  `[sp,#4]`=arg5, … (the callee's `push {r4-r8,lr}` + `sub sp`
                  then place arg k at `[sp, frame_size+24+(k-4)*4]`).
and asserts the result matches wasmtime ground truth. Symbols come from the ELF
symtab (SHT_SYMTAB), not host-dependent disasm text.

INCOMING is the falcon-relevant path (func_57/func_58 are >8-param leaves); a HIGH
param count (sum25, reading param 24) is included so a high-index stack read is
actually exercised, not just a 10-param case with all-small offsets. An OUTGOING
case (a caller passing 10 args through a callee) exercises `emit_stack_args` +
the lifted outgoing cap; its internal BL is hooked (relocatable leaves it
unresolved).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/stack_args_503_differential.py
Exits nonzero on any mismatch or fault.
"""
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_SP,
)

SYNTH = os.environ.get("SYNTH", "./target/release/synth")
ARG_REGS = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)

CODE, STK, RET = 0x100000, 0x900000, 0x300000

# Each fixture: a .wat string, the export name, and a list of (args...) vectors.
SUM10 = """(module (func (export "sum10")
  (param i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
  local.get 0 local.get 1 i32.add local.get 2 i32.add local.get 3 i32.add
  local.get 4 i32.add local.get 5 i32.add local.get 6 i32.add local.get 7 i32.add
  local.get 8 i32.add local.get 9 i32.add))"""

# 25 params; reads a HIGH index (24) and a mid index (12) to exercise large
# incoming offsets, not just the first stack slot.
SUM25 = "(module (func (export \"sum25\") (param" + " i32" * 25 + """) (result i32)
  local.get 0 local.get 24 i32.add local.get 12 i32.add local.get 9 i32.add))"""

# Outgoing: caller passes 10 args to callee (exercises emit_stack_args + the
# lifted outgoing cap). callee returns a discriminating combination.
CALL10 = """(module
  (func $callee (param i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
    local.get 0 local.get 4 i32.add local.get 9 i32.add local.get 5 i32.sub)
  (func (export "caller") (param i32) (result i32)
    local.get 0
    i32.const 10 i32.const 20 i32.const 30 i32.const 40
    i32.const 50 i32.const 60 i32.const 70 i32.const 80 i32.const 90
    call $callee))"""

# Combined: a 6-param function that BOTH reads its own incoming stack params
# (4,5) AND makes a 6-arg call passing those same incoming params on the outgoing
# stack. This is the realistic falcon shape (func_57/58 are unlikely pure leaves)
# and the only path where the incoming-offset formula `frame_size+24+(k-4)*4` has
# to correctly skip over the `outgoing_arg_bytes` region that also lives in
# `frame_size`. params 4,5 are read again AFTER the call to confirm the incoming
# region (above the frame) survives the inner call's use of the outgoing region
# (at the frame bottom).
BOTH = """(module
  (func $g (param i32 i32 i32 i32 i32 i32) (result i32)
    local.get 0 local.get 4 i32.add local.get 5 i32.add)
  (func (export "both") (param i32 i32 i32 i32 i32 i32) (result i32)
    local.get 0 local.get 1 local.get 2 local.get 3 local.get 4 local.get 5
    call $g
    local.get 4 i32.add
    local.get 5 i32.add))"""


def compile_reloc(wat_text, elf):
    wat = elf + ".wat"
    Path(wat).write_text(wat_text)
    r = subprocess.run(
        [SYNTH, "compile", wat, "-o", elf, "--target", "cortex-m4",
         "--all-exports", "--relocatable"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"compile failed/skipped for {elf}:\n{r.stderr}")
    return wat


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return code, base, syms


def wasmtime_run(wat_text, export, args):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wat_text)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    signed = [a - (1 << 32) if a >= 1 << 31 else a for a in args]
    return inst.exports(st)[export](st, *signed) & 0xFFFFFFFF


def unicorn_run(code, base, faddr, args, bl_hook_target=None):
    """Run faddr with AAPCS args. Returns r0, or 'ERR:...'. bl_hook_target, if
    set, redirects the first internal BL to that function address (for the
    relocatable outgoing case where the BL is unresolved).

    Symbol values may carry the Thumb bit (odd), so mask it for byte offsets and
    re-add it only for the PC."""
    foff = (faddr & ~1) - base  # file/byte offset (Thumb bit masked)
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    for r in ARG_REGS:
        mu.reg_write(r, 0)
    for r, v in zip(ARG_REGS, args):
        mu.reg_write(r, v & 0xFFFFFFFF)
    # args 4..N pushed so [sp,#0]=arg4, [sp,#4]=arg5, ... at entry.
    stack_args = args[len(ARG_REGS):]
    sp = STK
    if stack_args:
        # 8-byte align the outgoing block (AAPCS), room for all stack args.
        block = (len(stack_args) * 4 + 7) & ~7
        sp = STK - block
        for i, v in enumerate(stack_args):
            mu.mem_write(sp + i * 4, struct.pack("<I", v & 0xFFFFFFFF))
    mu.reg_write(UC_ARM_REG_SP, sp)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)

    if bl_hook_target is not None:
        md = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        # find the first bl in the caller body (disasm from the masked offset)
        bl_at = next((i.address for i in md.disasm(bytes(code[foff:]),
                                                   faddr & ~1) if i.mnemonic == "bl"),
                     None)
        tgt = CODE + ((bl_hook_target & ~1) - base)

        def hook(uc, address, size, ud):
            if bl_at is not None and address == CODE + (bl_at - base):
                uc.reg_write(UC_ARM_REG_LR, (address + 4) | 1)
                uc.reg_write(UC_ARM_REG_PC, tgt | 1)
        mu.hook_add(UC_HOOK_CODE, hook)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=200000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    fails = 0

    # ---- INCOMING: sum10 ----
    elf = "/tmp/sa503_sum10.elf"
    wat = compile_reloc(SUM10, elf)
    code, base, syms = load(elf)
    fa = syms.get("sum10") or syms["func_0"]
    wt_text = Path(wat).read_text()
    for vec in [tuple(range(10)), (5,) * 10, (100, 200, 300, 400, 500, 600, 700,
                800, 900, 1000), (0x7FFFFFFF, 1, 0, 0, 0, 0, 0, 0, 0, 1)]:
        exp = wasmtime_run(wt_text, "sum10", vec)
        got = unicorn_run(code, base, fa, vec)
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        g = f"0x{got:08X}" if isinstance(got, int) else got
        print(f"{'OK  ' if ok else 'FAIL'} sum10{vec} = {g} (wasmtime 0x{exp:08X})")

    # ---- INCOMING: sum25 (high-index reads) ----
    elf = "/tmp/sa503_sum25.elf"
    wat = compile_reloc(SUM25, elf)
    code, base, syms = load(elf)
    fa = syms.get("sum25") or syms["func_0"]
    wt_text = Path(wat).read_text()
    for vec in [tuple(range(25)), tuple(range(100, 125)),
                tuple((i * 7 + 3) & 0xFFFF for i in range(25))]:
        exp = wasmtime_run(wt_text, "sum25", vec)
        got = unicorn_run(code, base, fa, vec)
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        g = f"0x{got:08X}" if isinstance(got, int) else got
        print(f"{'OK  ' if ok else 'FAIL'} sum25(0..24 variant) = {g} "
              f"(wasmtime 0x{exp:08X})")

    # ---- OUTGOING: caller passes 10 args through callee ----
    elf = "/tmp/sa503_call10.elf"
    wat = compile_reloc(CALL10, elf)
    code, base, syms = load(elf)
    caller = syms["caller"] if "caller" in syms else syms["func_1"]
    callee = syms["func_0"]
    wt_text = Path(wat).read_text()
    for vec in [(0,), (1000,), (0x7FFFFFFF,)]:
        exp = wasmtime_run(wt_text, "caller", vec)
        got = unicorn_run(code, base, caller, vec, bl_hook_target=callee)
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        g = f"0x{got:08X}" if isinstance(got, int) else got
        print(f"{'OK  ' if ok else 'FAIL'} caller{vec} = {g} (wasmtime 0x{exp:08X})")

    # ---- COMBINED: >4 incoming params AND a >4-arg call in one function ----
    # The incoming offset must skip over the outgoing-arg region (both live in
    # frame_size). 'both'=func_1 calls $g=func_0.
    elf = "/tmp/sa503_both.elf"
    wat = compile_reloc(BOTH, elf)
    code, base, syms = load(elf)
    both = syms["both"] if "both" in syms else syms["func_1"]
    g = syms["func_0"]
    wt_text = Path(wat).read_text()
    for vec in [(1, 2, 3, 4, 5, 6), (10, 20, 30, 40, 50, 60),
                (0x7FFFFFFF, 0, 0, 0, 1, 2)]:
        exp = wasmtime_run(wt_text, "both", vec)
        got = unicorn_run(code, base, both, vec, bl_hook_target=g)
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        gs = f"0x{got:08X}" if isinstance(got, int) else got
        print(f"{'OK  ' if ok else 'FAIL'} both{vec} = {gs} (wasmtime 0x{exp:08X})")

    print("\nORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
