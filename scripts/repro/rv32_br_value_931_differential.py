#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 16
"""#931 (CRITICAL) — RV32 `br` out of a value-producing `block` discarded its value.

The RV32 selector lowered `br` as a bare `jal` and moved nothing. `br` also does
not pop, so the branch's value stayed on the vstack; the fallthrough expression
then allocated a DIFFERENT register to avoid the live one, and the merge read
that one. The block therefore yielded the not-taken path's value. Measured on
v0.55.0 for `(block $exit (result i32) (br $exit (i32.const 1)) (i32.const 0))`:

      0: li  t0, 0x1     ; br $exit's value -> t0
      4: j   0xc         ; br $exit -> merge
      8: li  t1, 0x0     ; fallthrough value -> t1
      c: mv  a0, t1      ; merge reads t1, NOT t0
     10: ret

`synth compile` exits 0 with no warning. This is the most basic form of
structured control flow with a value, so the blast radius covers `block`,
`switch`-style dispatch, and label shadowing alike (8 `labels.wast` assertions).

The fix reconciles every exit edge onto the frame's canonical result register —
the same join #343 already performed for `if`/`else` arms, never applied to `br`
edges. This oracle EXECUTES each export under unicorn (UC_ARCH_RISCV /
UC_MODE_RISCV32, ILP32) and compares against wasmtime, so it grades the value
the hardware would actually return rather than the shape of the disassembly.

Symbols come from the ELF `.symtab` (SHT_SYMTAB), not `synth disasm` text: the
disassembler is host-dependent and its rendering is not a reliable symbol
source.

Run:
  synth compile scripts/repro/rv32_br_value_931.wat -b riscv \
        --target riscv32imac --relocatable --all-exports -o /tmp/br931.o
  /tmp/synthvenv/bin/python \
        scripts/repro/rv32_br_value_931_differential.py /tmp/br931.o
"""

import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/rv32_br_value_931.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/br931.o"

CODE, LIN, RET = 0x100000, 0x40000, 0x200000

# Functions returning i64 hand the result back in the a0:a1 pair (lo:hi) per
# RV32 ILP32; the harness reads both halves and compares masked to 64 bits.
I64_FUNCS = {"br64"}

# (export, args). Every value-carrying shape is exercised on BOTH the branch
# edge and the fallthrough edge where it has one — a fix that reconciled only
# one direction would pass a single-edge vector.
VECTORS = [
    # The issue as filed: pre-fix returns 0.
    ("simple", ()),
    # Computed branch value — the edges differ for a reason other than
    # allocation order.
    ("computed", (0,)),
    ("computed", (32,)),
    # The canonical-register hazard: a promoted local donating its register
    # would be clobbered by the fallthrough reconciliation (35 -> 28).
    ("promoted", ()),
    # br_if, both edges.
    ("brif", (1,)),
    ("brif", (0,)),
    ("brif", (99,)),
    # Two value-carrying edges into one frame + its fallthrough.
    ("two_edges", (0,)),
    ("two_edges", (1,)),
    ("two_edges", (5,)),
    # i64 — a dropped hi-move corrupts the top 32 bits.
    ("br64", ()),
    # A value live across the block: over-truncating at the `br` would eat it.
    ("carried", ()),
    # Arity-0 `br` must keep working (and stay byte-identical).
    ("cfonly", (1,)),
    ("cfonly", (0,)),
    # #930's shape on RV32 — correct today by luck; pin it.
    ("nested", ()),
    # Value-carrying `br 1` to an OUTER frame, both edges.
    ("outer", (1,)),
    ("outer", (0,)),
]


def symbols(path):
    with open(path, "rb") as fh:
        f = ELFFile(fh)
        st = f.get_section_by_name(".symtab")
        syms = {}
        for s in st.iter_symbols():
            if s.name and s["st_info"]["type"] == "STT_FUNC":
                syms[s.name] = s["st_value"]
        return syms, f.get_section_by_name(".text").data()


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    def wt(name, args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        mask = 0xFFFFFFFFFFFFFFFF if name in I64_FUNCS else 0xFFFFFFFF
        return inst.exports(store)[name](store, *args) & mask

    syms, code = symbols(ELF)

    def run(name, args):
        addr = syms.get(name)
        if addr is None:
            return None, f"symbol {name} missing (function skipped?)"
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        for base, size in [(CODE, 0x20000), (LIN, 0x20000), (0x88000, 0x10000), (RET, 0x1000)]:
            mu.mem_map(base, size)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, 0x90000)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        for i, a in enumerate(args):
            mu.reg_write(UC_RISCV_REG_A0 + i, a & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + addr, RET, count=4000)
        except UcError as e:
            return None, str(e)
        lo = mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
        if name in I64_FUNCS:
            hi = mu.reg_read(UC_RISCV_REG_A1) & 0xFFFFFFFF
            return lo | (hi << 32), ""
        return lo, ""

    fails = 0
    for name, args in VECTORS:
        gt = wt(name, args)
        res, err = run(name, args)
        ok = res == gt
        fails += 0 if ok else 1
        shown = f"0x{res:08x}={res}" if res is not None else f"ERR({err})"
        shown_args = ", ".join(str(a) for a in args)
        print(f"{name}({shown_args}) = {shown}  wasmtime=0x{gt:08x}={gt}  {'OK' if ok else 'FAIL'}")

    # NON-VACUITY: every vector must have executed. A missing symbol or a
    # selector decline would otherwise reduce this oracle to a green zero.
    print(f"\n#931 EMULATIONS={len(VECTORS)}")
    print(
        "RISC-V br-value #931 ORACLE: PASS"
        if not fails
        else f"RISC-V br-value #931 ORACLE: FAIL ({fails})"
    )
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
