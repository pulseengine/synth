#!/usr/bin/env python3
"""#509 (epic #242) — CHARACTERIZE the value-returning-branch miscompile.

The oracle-first artifact for #509: the DIRECT selector (so the SHIPPED
`--relocatable` path) drops the CARRIED VALUE of a value-returning branch. A
`br`/`br_if`/`br_table` that targets a result-typed block and carries an operand
returns 0 (value lost) for the dispatched/taken arm; wasmtime keeps it. This does
NOT change codegen — it compiles the in-tree `br_value_509.wat`, runs each export
under unicorn (UC_ARCH_ARM / Thumb), and compares to wasmtime, on BOTH the direct
(`--relocatable`) and default paths.

ROOT CAUSE (per #509 / the roadmap): the IR carries no block-result arity
(`WasmOp::Block` is a unit variant; the decoder tracks none), so the selector
cannot thread a carried value to the block join. The #507 decline-to-direct
shortcut does NOT apply (it cannot distinguish a CARRIED result from an UNWOUND
void-target value, and over-refuses valid void code). The real fix threads
block-result arity (decoder -> WasmOp::Block/Loop/If -> selector) plus a
result-register convention generalizing the #313 if/else reconciliation —
byte-changing, background-priority, its own gated step (NOT an idle tick).

DISCRIMINATOR / non-vacuity: `ctrl` is a value-returning block with NO branch —
its value flows straight to the block end and is lowered correctly. So a failure
isolates to the branch value-carry, not result-typed blocks in general. While the
bug is live, `pick`/`pick_brif` diverge on the dispatched/taken arm and `ctrl`
stays correct; this script EXITS 0 when that characterization holds and 1 if
reality diverges from it (e.g. `ctrl` broke, or a value-carry case silently
started matching — which, without the real fix, would mean the harness went
blind). When the fix lands, flip EXPECT_MISCOMPILE->False and the same script
becomes the correctness gate (every path must then match wasmtime).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/br_table_value_509_differential.py
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
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("br_value_509.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x900000, 0x300000

# Flipped to False by the #509 fix PR (blocktype-arity side-table + designated
# result register per value block in `select_with_stack`, plus the #507-style
# detect-and-route-to-direct for value-carrying br/br_if on the optimized
# path): the script now enforces correctness — every edge (taken, dispatched,
# and fall-through) on BOTH paths must match wasmtime. Pre-fix recorded wrong
# values (direct path): pick(1/2/5)->2 vs 12, pick_brif(1/7)->0 vs 10,
# pick_br(0/1/7)->0 vs 30/31/37, pick_br_fall(1/7)->0 vs 10.
EXPECT_MISCOMPILE = False

# (export, args) — the dispatched/taken arms are the value-carry cases.
CASES = [
    ("pick", [0, 1, 2, 5]),       # br_table; sel>=1 dispatched arms drop the carry
    ("pick_brif", [0, 1, 7]),     # br_if; taken (arg!=0) arms drop the carry
    ("pick_br", [0, 1, 7]),       # plain br; always-taken edge drops the carry
    ("pick_br_fall", [0, 1, 7]),  # br (taken, arg!=0) + real fall-through (arg==0)
    ("ctrl", [0, 1, 7]),          # branchless value block — control, must stay OK
]
VALUE_CARRY_FNS = {"pick", "pick_brif", "pick_br", "pick_br_fall"}


def wasmtime_run(fn, arg):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, arg)


def compile_synth(out, relocatable):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"compile failed/skipped (reloc={relocatable}): {r.stderr}")


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
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def run_path(label, relocatable):
    out = f"/tmp/br509_{'rel' if relocatable else 'opt'}.o"
    compile_synth(out, relocatable)
    code, base, syms = load(out)
    print(f"\n=== {label} path ===")
    carry_div = 0
    ctrl_ok = True
    for fn, args in CASES:
        faddr = syms.get(fn)
        if faddr is None:
            print(f"  {fn}: SYMBOL MISSING")
            if fn in VALUE_CARRY_FNS:
                carry_div += 1
            else:
                ctrl_ok = False
            continue
        for arg in args:
            exp = wasmtime_run(fn, arg)
            got = unicorn_run(code, base, faddr, arg)
            match = isinstance(got, int) and got == exp
            if not match:
                if fn in VALUE_CARRY_FNS:
                    carry_div += 1
                else:
                    ctrl_ok = False
            print(f"  [{'ok ' if match else 'BUG'}] {fn}({arg}) -> {got} "
                  f"(wasmtime {exp})"
                  + ("" if match else "  [carried value dropped]"))
    return carry_div, ctrl_ok


def main():
    rel_div, rel_ctrl = run_path("DIRECT (--relocatable / shipped)", relocatable=True)
    opt_div, opt_ctrl = run_path("DEFAULT (optimized)", relocatable=False)

    print("\n--- characterization verdict ---")
    if EXPECT_MISCOMPILE:
        ok = rel_div > 0 and rel_ctrl and opt_ctrl
        print(f"direct value-carry divergences={rel_div} (ctrl_ok={rel_ctrl})  "
              f"default ctrl_ok={opt_ctrl} (value-carry div={opt_div})")
        if ok:
            print("RESULT: PASS — #509 reproduces: a value carried over a branch to "
                  "a result-typed block is dropped on the SHIPPED direct path, while "
                  "the branchless control stays correct. Oracle ready for the gated "
                  "block-arity fix.")
            sys.exit(0)
        print("RESULT: FAIL — reality diverged from the #509 root cause (the "
              "branchless control broke, or value-carry stopped miscompiling on the "
              "direct path). Re-examine before trusting the fix spec.")
        sys.exit(1)
    else:
        total = rel_div + opt_div + (0 if rel_ctrl else 1) + (0 if opt_ctrl else 1)
        if total == 0:
            print("RESULT: PASS — every value-returning branch now matches wasmtime "
                  "on both paths. #509 fixed.")
            sys.exit(0)
        print(f"RESULT: FAIL — {total} residual divergence(s); #509 not fully fixed.")
        sys.exit(1)


if __name__ == "__main__":
    main()
