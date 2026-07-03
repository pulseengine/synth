#!/usr/bin/env python3
"""#503-i64 — AAPCS 64-bit STACK-param differential oracle (epic #242).

Compiles `i64_stack_param_503.wat` — every shape of the previously-declined
"#518/#503: an i64/f64 param is AAPCS-passed past R3" class plus the
narrow-after-wide stack-param shape that was silently MIScompiled (p3 of
`(i64 i32 i32 i32)` read from R3 = p2) — on BOTH lowering paths:

  * DIRECT     (`--relocatable`)          — the shipped/falcon path
                                            (`select_with_stack`).
  * OPTIMIZED  (default `--target ...`)   — wide-param signatures are routed
                                            to the direct selector (#503-i64),
                                            so this exercises the route.

and runs each export under unicorn with TRUE-AAPCS argument placement:
r0..r3 walked with even-aligned i64 pairs, stack args written at entry SP
(narrow: 4-byte NSAA; wide: 8-byte-aligned NSAA). wasmtime is ground truth;
i64 results are read from r0 (lo) : r1 (hi).

Exits nonzero on any divergence or any skipped export, so it can gate CI.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/synthvenv/bin/python \
      scripts/repro/i64_stack_param_503_differential.py
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
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("i64_stack_param_503.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET, R11 = 0x100000, 0x900000, 0x300000, 0x20000000

# (export, args, signature). The signature drives TRUE-AAPCS placement:
# registers first (even-aligned pairs for i64), then the entry-SP stack
# (NSAA: 4-byte for i32, 8-byte-aligned for i64) — matching what a real
# AAPCS caller would do, NOT what synth happens to emit.
CASES = [
    ("s_mix", (1, 2, 3, 4, 0x1_0000_0007), "i32,i32,i32,i32,i64"),
    ("s_mix", (0xFFFFFFFF, 0, 0, 0, 0xFFFFFFFF_00000001), "i32,i32,i32,i32,i64"),
    ("s_align", (1, 2, 3, 4, 5, 0x55555555_00000003), "i32,i32,i32,i32,i32,i64"),
    ("s_p3", (9, 8, 7, 0xA5A5A5A5_5A5A5A5A), "i32,i32,i32,i64"),
    ("s_nar", (0x1_00000001, 5, 100, 42), "i64,i32,i32,i32"),
    ("s_call", (1, 40, 3, 4, 0x7_00000009), "i32,i32,i32,i32,i64"),
    ("s_wr", (1, 2, 3, 4, 0xFFFFFFFF), "i32,i32,i32,i32,i64"),
    ("s_i32", (7,), "i32"),
]
I64_RESULT = {"s_mix", "s_align", "s_p3", "s_call", "s_wr"}


def to_signed(v, wide):
    bits = 64 if wide else 32
    return v - (1 << bits) if v >= (1 << (bits - 1)) else v


def wasmtime_run(fn, args, sig):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    sargs = [to_signed(a, t == "i64") for a, t in zip(args, sig.split(","))]
    res = inst.exports(store)[fn](store, *sargs)
    return res & (0xFFFFFFFFFFFFFFFF if fn in I64_RESULT else 0xFFFFFFFF)


def compile_synth(out, relocatable):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed (reloc={relocatable}): {r.stderr}")
    return r.stderr


def encode_thm_bl(pc, target):
    """Thumb-2 BL: encode (target - (pc+4)) as the S/J1/J2/imm10/imm11 form."""
    off = target - (pc + 4)
    off &= 0x1FFFFFF  # 25-bit signed range
    s = (off >> 24) & 1
    i1 = (off >> 23) & 1
    i2 = (off >> 22) & 1
    imm10 = (off >> 12) & 0x3FF
    imm11 = (off >> 1) & 0x7FF
    j1 = (~i1 & 1) ^ s
    j2 = (~i2 & 1) ^ s
    hw1 = 0xF000 | (s << 10) | imm10
    hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
    return hw1, hw2


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text_sec = f.get_section_by_name(".text")
    code, base = bytearray(text_sec.data()), text_sec["sh_addr"]
    syms = {}
    symtab = None
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            symtab = sec
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    # --relocatable object: resolve internal THM_CALLs (s_call -> $helper) in
    # place, exactly as `ld` would — the emulator runs raw .text bytes.
    rel = f.get_section_by_name(".rel.text")
    if rel is not None and symtab is not None:
        for r in rel.iter_relocations():
            t = r["r_info_type"]
            if t in (10, 30):  # R_ARM_THM_CALL / R_ARM_THM_JUMP24
                sym = symtab.get_symbol(r["r_info_sym"])
                target = CODE + (sym["st_value"] & ~1)
                pc = CODE + r["r_offset"]
                hw1, hw2 = encode_thm_bl(pc, target)
                struct.pack_into("<HH", code, r["r_offset"], hw1, hw2)
    return bytes(code), base, syms


def place_args(mu, args, sig):
    """TRUE AAPCS: r0..r3 (even-aligned pairs), then the entry-SP stack."""
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
    ncrn, nsaa = 0, 0
    for v, t in zip(args, sig.split(",")):
        if t == "i64":
            if ncrn % 2:
                ncrn += 1
            if ncrn <= 2:
                mu.reg_write(regs[ncrn], v & 0xFFFFFFFF)
                mu.reg_write(regs[ncrn + 1], (v >> 32) & 0xFFFFFFFF)
                ncrn += 2
            else:
                ncrn = 4  # C.5: no back-fill
                if nsaa % 8:
                    nsaa += 4
                mu.mem_write(STK + nsaa, (v & 0xFFFFFFFFFFFFFFFF)
                             .to_bytes(8, "little"))
                nsaa += 8
        elif ncrn <= 3:
            mu.reg_write(regs[ncrn], v & 0xFFFFFFFF)
            ncrn += 1
        else:
            ncrn = 4
            mu.mem_write(STK + nsaa, (v & 0xFFFFFFFF).to_bytes(4, "little"))
            nsaa += 4


def unicorn_run(code, base, faddr, args, sig, i64_result):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)  # entry SP == first stack arg (AAPCS)
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
    out = f"/tmp/i503_{'rel' if relocatable else 'opt'}.o"
    stderr = compile_synth(out, relocatable)
    fails = 0
    if "skipping function" in stderr:
        print(f"  FAIL: a function was skipped on the {label} path:\n{stderr}")
        fails += 1
    code, base, syms = load(out)
    print(f"\n=== {label} path ===")
    for fn, args, sig in CASES:
        faddr = syms.get(fn)
        if faddr is None:
            print(f"  [BUG] {fn}: SYMBOL MISSING")
            fails += 1
            continue
        exp = wasmtime_run(fn, args, sig)
        got = unicorn_run(code, base, faddr, args, sig, fn in I64_RESULT)
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        print(f"  [{'ok ' if ok else 'BUG'}] {fn}{args} -> "
              f"{got:#x}" if isinstance(got, int) else got,
              f" (wasmtime {exp:#x})")
    return fails


def main():
    fails = run_path("DIRECT (--relocatable)", relocatable=True)
    fails += run_path("OPTIMIZED (default, wide-param route)", relocatable=False)
    print("\n--- verdict ---")
    if fails == 0:
        print("RESULT: PASS — every previously-declined i64-stack-param shape "
              "(and the narrow-after-wide miscompile shape) compiles on both "
              "paths and matches wasmtime.")
        sys.exit(0)
    print(f"RESULT: FAIL — {fails} divergence(s)/missing symbol(s).")
    sys.exit(1)


if __name__ == "__main__":
    main()
