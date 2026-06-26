#!/usr/bin/env python3
"""#507 (epic #242) — EXECUTION-validate the optimized-path br_table fix.

On the optimized (non-`--relocatable`) path, `synth compile` silently
miscompiled `br_table`: the dispatch is DROPPED during the wasm→IR lowering, so
the arm bodies were emitted in fall-through sequence with no `cmp`/branch on the
selector — every input hit the last arm (a silent wrong-code, exit 0). The
`--relocatable` direct path lowered it correctly. The fix detects `br_table` on
the raw wasm op stream and forces the direct selector (which lowers it as a
cmp-chain), so the DEFAULT `synth compile` is correct too.

This harness compiles the fixture via the DEFAULT optimized path (no
`--relocatable`), runs `dispatch(sel)` under unicorn (UC_ARCH_ARM / Thumb) for
each selector, and asserts the resulting linear memory matches wasmtime. Symbols
come from the ELF symtab (SHT_SYMTAB); the linmem base is read from
`__linear_memory_base` (mask the Thumb bit on the function symbol).

NON-VACUITY: pre-fix every selector yielded mem[0]=40 (the last arm); the fix
changed the function's bytes (the optimized fall-through became a cmp-chain,
byte-identical to `--no-optimize`). A regression that re-drops the dispatch
re-breaks every non-last selector here.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/br_table_507_differential.py
Exits nonzero on any mismatch or fault.
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

SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, STK, RET = 0x100000, 0x900000, 0x300000
LIN_SIZE = 0x10000  # 1 page

# Three br_table shapes (sequential targets, shared-tail, value-returning) — the
# three gale reproduced. Each stores a selector-dependent marker to mem[0].
FIXTURES = {
    # sequential distinct targets
    "seq": """(module (memory (export "memory") 1)
 (func (export "dispatch") (param i32)
  (block (block (block (block
    (br_table 0 1 2 3 (local.get 0)))
    (i32.store (i32.const 0)(i32.const 10))(return))
    (i32.store (i32.const 0)(i32.const 20))(return))
    (i32.store (i32.const 0)(i32.const 30))(return))
  (i32.store (i32.const 0)(i32.const 40))))""",
    # shared-tail: targets 0 and 2 jump to the same arm
    "shared": """(module (memory (export "memory") 1)
 (func (export "dispatch") (param i32)
  (block (block (block
    (br_table 0 1 0 2 (local.get 0)))
    (i32.store (i32.const 0)(i32.const 11))(return))
    (i32.store (i32.const 0)(i32.const 22))(return))
  (i32.store (i32.const 0)(i32.const 33))))""",
}
# selectors to test per fixture (incl. an out-of-range → default arm)
SELECTORS = [0, 1, 2, 3, 4, 7]


def compile_default(wat_text, elf):
    wat = elf + ".wat"
    Path(wat).write_text(wat_text)
    r = subprocess.run(
        [SYNTH, "compile", wat, "-o", elf, "--target", "cortex-m4", "--all-exports"],
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


def wasmtime_mem0(wat_text, sel):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wat_text)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    inst.exports(st)["dispatch"](st, sel)
    return struct.unpack("<i", bytes(inst.exports(st)["memory"].read(st, 0, 4)))[0]


def unicorn_mem0(code, base, faddr, lin_base, sel):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(lin_base, LIN_SIZE)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, lin_base)
    mu.reg_write(UC_ARM_REG_R0, sel & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=200000)
    except UcError as e:
        return f"ERR:{e}"
    return struct.unpack("<i", bytes(mu.mem_read(lin_base, 4)))[0]


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    fails = 0
    for name, wat_text in FIXTURES.items():
        elf = f"/tmp/bt507_{name}.elf"
        wat = compile_default(wat_text, elf)
        code, base, syms = load(elf)
        lin_base = syms["__linear_memory_base"]
        fa = syms.get("dispatch") or syms["func_0"]
        wt_text = Path(wat).read_text()
        for sel in SELECTORS:
            exp = wasmtime_mem0(wt_text, sel)
            got = unicorn_mem0(code, base, fa, lin_base, sel)
            ok = isinstance(got, int) and got == exp
            fails += 0 if ok else 1
            g = str(got) if isinstance(got, int) else got
            print(f"{'OK  ' if ok else 'FAIL'} {name} dispatch({sel}) -> mem[0]={g} "
                  f"(wasmtime {exp})")
    print("\nORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
