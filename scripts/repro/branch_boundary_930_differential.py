#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 16
"""#930 — thumb-2 branch target lands mid-instruction (labels.wast br / br_if2).

A `br`/`br_if` exiting an enclosing block FROM INSIDE an `if`, whose value
operand is itself a block-that-branches, silently produced the wrong value on
thumb-2 (exit 0, no diagnostic). Root cause: `select_with_stack`'s `End`
handler decided "this End closes an if" by looking at `if_labels` ALONE, so
the `End` of a plain block nested inside a then/else arm was misattributed to
the enclosing `if` — the if's else/end labels were emitted at the inner
block's position, the wrong stacks were popped, and the inner block's own end
label was NEVER emitted. Its `B .Lblock_end_N` then stayed an unresolved
`b #0` placeholder whose target (pc+4) fell on the SECOND halfword of the
following 32-bit `movw`: the br_if condition register was never written and
the CPU executed a halfword that was never an instruction. Sibling of #740
(B<cond>.W T3 offset halved) — the same SC-5 sentence, "branch offset
calculation shall account for Thumb instruction alignment and variable
instruction widths".

The same misattribution ALSO mis-placed the if's else label at the inner
block's position — a boundary-VALID but semantically wrong `beq` target on the
condition-false path. `brif2p(0)` pins that half; the instruction-start-set
invariant alone cannot see it.

This oracle EXECUTES each export under unicorn (thumb) and compares against
wasmtime, on BOTH ARM codegen paths — `--relocatable` forces the direct
selector (`select_with_stack`, the path #740 was on and #930 is on) and the
default standalone image takes the optimized path. Scratch registers are
seeded with a nonzero sentinel so a "reset value" read is observably wrong
rather than a lucky zero.

Symbols come from the ELF `.symtab` (SHT_SYMTAB), not `synth disasm` text.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/branch_boundary_930_differential.py
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
    UC_ARM_REG_R4,
    UC_ARM_REG_R5,
    UC_ARM_REG_R6,
    UC_ARM_REG_R7,
    UC_ARM_REG_R8,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("branch_boundary_930.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE = 0x0
SP_INIT = 0x2004_0000
SENTINEL = 0xA5A5_A5A5  # "reset value" that is loudly wrong, never a lucky 0

# (export, args) — labels.wast br_if2 / br as filed, plus both edges of the
# enclosing if (brif2p) and of the br_if itself (brifc).
VECTORS = [
    ("brif2", ()),
    ("br", ()),
    ("brif2p", (1,)),
    ("brif2p", (0,)),
    ("brifc", (1,)),
    ("brifc", (0,)),
    ("brifc", (7,)),
    ("brifc", (0xA5A5A5A5,)),
]


def compile_elf(out, relocatable):
    args = [SYNTH, "compile", str(WAT), "-b", "arm", "-t", "cortex-m3",
            "--all-exports", "-o", out]
    if relocatable:
        args.append("--relocatable")
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"compile failed ({'relocatable' if relocatable else 'default'}): "
                 f"{r.stderr}")


def load(elf):
    with open(elf, "rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text").data()
        syms = {}
        for sec in f.iter_sections():
            if sec.header.sh_type == "SHT_SYMTAB":
                for s in sec.iter_symbols():
                    if s.name and s["st_info"]["type"] == "STT_FUNC":
                        syms[s.name] = s["st_value"]
        return text, syms


def run_unicorn(text, faddr, args):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(0x2000_0000, 0x8_0000)
    mu.mem_write(CODE, text)
    mu.reg_write(UC_ARM_REG_SP, SP_INIT)
    # Seed every scratch/callee-saved register the fixtures touch with a
    # nonzero sentinel: the pre-fix miscompile READS a never-written register
    # ("its movw was skipped over"), and a zero-initialised emulator can grade
    # that read as a lucky PASS.
    for reg in (UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4,
                UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7, UC_ARM_REG_R8):
        mu.reg_write(reg, SENTINEL)
    ret = CODE + 0xFF00
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    for i, a in enumerate(args):
        mu.reg_write(UC_ARM_REG_R0 + i, a & 0xFFFFFFFF)
    if not args:
        mu.reg_write(UC_ARM_REG_R0, SENTINEL)
    try:
        mu.emu_start((faddr & ~1) | 1, ret, timeout=5_000_000, count=100_000)
    except UcError as e:
        return None, str(e)
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF, ""


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_bytes())

    def wt(name, args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[name](store, *args) & 0xFFFFFFFF

    fails = 0
    executed = 0
    for label, relocatable in [("direct/--relocatable", True),
                               ("optimized/default", False)]:
        out = f"/tmp/branch_boundary_930_{'rel' if relocatable else 'std'}.o"
        compile_elf(out, relocatable)
        text, syms = load(out)
        print(f"--- path: {label} ---")
        for name, args in VECTORS:
            gt = wt(name, args)
            faddr = syms.get(name)
            if faddr is None:
                fails += 1
                print(f"FAIL {name}{args}: symbol missing (function skipped?)")
                continue
            res, err = run_unicorn(text, faddr, args)
            ok = res == gt
            fails += 0 if ok else 1
            executed += 1 if res is not None else 0
            shown = f"0x{res:08x}" if res is not None else f"ERR({err})"
            shown_args = ", ".join(str(a) for a in args)
            print(f"{'OK  ' if ok else 'FAIL'} {name}({shown_args}) = {shown} "
                  f"(wasmtime 0x{gt:08x})")

    # NON-VACUITY, ASSERTED: every vector must actually reach the emulator on
    # BOTH paths — a decline or a skipped function must not green this gate.
    total = 2 * len(VECTORS)
    print(f"\n#930 EMULATIONS={executed}/{total}")
    if executed != total:
        print(f"FAIL: only {executed} of {total} vectors reached the emulator")
        sys.exit(1)
    print("ARM branch-boundary #930 ORACLE:", "PASS" if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
