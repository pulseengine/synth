#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 141
"""RQ-89-BRVALUE (#1215) — a value-carrying branch in an OPERAND position,
executed on all three ARM legs against wasmtime.

# The defect (measured on v0.88.0, 0161dee1, before this oracle)

Eleven spec assertions across five functions were SHARED-WRONG — both
selectors agreeing with each other and not with wasmtime — and were pinned in
`selector_parity_197_differential.py` under #1215. The default leg is no
second opinion here: every one of them is pre-gated to the direct selector
(`direct (pre-gate) br-table,value-carry`), so "both selectors" meant ONE
lowering, `select_with_stack`, reached two ways. Two mechanisms:

  1. The STACK MODEL after an unconditional transfer. Wasm's operand stack is
     polymorphic after `br`/`br_table`/`return`/`unreachable`; the direct
     selector's simulated stack is not, and a block's `end` never reset it to
     the block's entry height. The dead code after the transfer — the rest of
     a `br_table`'s operands, the rest of an enclosing expression — therefore
     left values on the model that no execution produces, and the code after
     the block consumed THEM instead of the outer values beneath:
     `br.wast nested-br_table-value-index` computed 4+8=12, wasmtime 1+8=9.
     Four of the five functions (10 assertions).
  2. A FUNCTION-LEVEL `br_table` edge landed its carried value in R0 BEFORE
     the dispatch cascade — and when the index itself lived in R0 (a
     `br_table` indexed by parameter 0) that landing overwrote the index, so
     every input dispatched as if it were the carried value: `func.wast
     break-br_table-nested-num(1)` returned 52, wasmtime 50.

# What this oracle executes

`brvalue_operand_1215.wat`: the nine spec functions in this family that the
fix touches (the five that were wrong, the two that the base compiler
REFUSED — `br_if.wast nested-br-value` / `nested-br_table-value`, VCR-RA-003
`JoinValueNotAvailable` — and now compile, and the two whose bytes moved,
`func.wast break-br_table-num` and `labels.wast switch`, the latter also
newly accepted), copied verbatim into one module; the two functions of
`rv32_br_value_931.wat` whose ARM bytes moved (that fixture is executed on
RV32 only, and its `carried` — `5 + (block (br 0 (i32.const 1)) (i32.const
0))` — was WRONG on all three ARM legs: 2, wasmtime 6); and four lane
fixtures that reach the same mechanism through a construct whose own `end` is
unreachable.
Each is compiled on the default, `--no-optimize` and `--relocatable` legs and
every vector is executed under unicorn and compared with wasmtime. The
`--relocatable` leg is the reason the functions are re-hosted at all: the spec
modules themselves are refused whole on that leg (#1052, global initializers),
so the parity oracle never executes it.

A trap is a trap on both sides: wasmtime `Trap` <=> the image stopping on its
`udf` (`UC_ERR_INSN_INVALID`).

# The refusal it pins

The reset in (1) is sound only when the dead code left the LIVE prefix as the
transfer left it. When the dead code pops BELOW the block's entry height the
model of the enclosing values is lost, and the selector refuses with a
`#1215:` diagnostic. `PBE_WAT` is that shape; every leg must skip it with that
needle. (The base compiler refused it too, with a bare `stack underflow`, so
this is not a newly refused shape — the byte census in the RQ-89-BRVALUE PR
found zero newly declined functions over tests/wast + the spec suite.)

# Red-first

Measured on the v0.88.0 binary (0161dee1): RED, `#1215 CHECKS=57/144`, the
same 29 failures on EACH of the three legs (`--relocatable` included) — 18
wrong values (the 11 spec vectors, the 6 `prop_block`/`prop_loop` vectors and
`repro931.carried`), 10 vectors of the three functions it refused, and the
`pbe` needle absent. On the fix: `144/144`, 141 emulations.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/brvalue_operand_1215_differential.py
"""
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_ERR_INSN_INVALID, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R11, UC_ARM_REG_SP

WAT = Path(__file__).with_name("brvalue_operand_1215.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET, MEM = 0x100000, 0x900000, 0x300000, 0x20000000
M32 = 0xFFFFFFFF

LEGS = (("default", []), ("no-optimize", ["--no-optimize"]), ("relocatable", ["--relocatable"]))

# (export, [args]) — the spec files' own assertion vectors for the spec
# functions; both branch directions and the out-of-range default for the
# lane fixtures.
CASES = [
    ("br.nested-br_table-value-index", [None]),
    ("br_table.nested-br_table-value", [0, 1, 2, 9, -9, 999999]),
    ("br_table.nested-br_table-value-index", [0, 1, 2, 3, -1000000, 9423975]),
    ("br_if.nested-br-value", [0, 1]),
    ("br_if.nested-br_table-value", [0, 1]),
    ("br_if.nested-br_table-value-index", [0, 1]),
    ("func.break-br_table-nested-num", [0, 1, 2, -100]),
    ("func.break-br_table-num", [0, 1, 10, -100]),
    ("labels.switch", [0, 1, 2, 3, 4, 5]),
    ("repro931.carried", [None]),
    ("repro931.promoted", [None]),
    ("prop_block", [0, 1, 5]),
    ("prop_loop", [0, 1, 5]),
    ("prop_return", [0, 1, 5]),
    ("prop_unreachable", [0, 1, 5]),
]

# Dead code popping BELOW the enclosing block's entry height: refused, loudly.
PBE_WAT = """(module
  (func (export "pbe") (param i32) (result i32)
    (i32.add (local.get 0)
      (i32.add (i32.const 100)
        (i32.add (i32.const 1)
          (block (result i32) (br 0 (i32.const 8)) (i32.add)))))))
"""
PBE_NEEDLE = "skipping function 'pbe': backend 'arm' failed: compilation failed: " \
             "instruction selection failed: Synthesis failed: #1215: unreachable code"


def compile_leg(src: Path, out: Path, extra: list[str], allow_skip: bool):
    cmd = [SYNTH, "compile", str(src), "-o", str(out), "--target", "cortex-m4", "--all-exports"] + extra
    if allow_skip:
        cmd.append("--allow-skipped-exports")
    return subprocess.run(cmd, capture_output=True, text=True)


def load(elf: Path):
    with elf.open("rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text")
        code, base = text.data(), text["sh_addr"]
        st = next(s for s in f.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        syms = {s.name: s["st_value"] for s in st.iter_symbols()
                if s.name and s["st_info"]["type"] == "STT_FUNC"}
    return code, base, syms


def emulate(code: bytes, base: int, faddr: int, arg):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, (len(code) + 0xFFFF) & ~0xFFFF)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_map(MEM, 0x10000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, MEM)
    mu.reg_write(UC_ARM_REG_R0, (arg or 0) & M32)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + (faddr & ~1) - base) | 1, RET, count=100_000)
    except UcError as e:
        return "trap" if e.errno == UC_ERR_INSN_INVALID else f"fault:{e}"
    if mu.reg_read(UC_ARM_REG_SP) != STK:
        return "sp-imbalance"
    return mu.reg_read(UC_ARM_REG_R0) & M32


def reference():
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, wasmtime.Module.from_file(engine, str(WAT)), [])
    ex = inst.exports(store)

    def call(fn, arg):
        try:
            r = ex[fn](store) if arg is None else ex[fn](store, arg)
        except wasmtime.Trap:
            return "trap"
        return r & M32
    return call


def main() -> int:
    ref = reference()
    checks = bad = 0
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        for leg, extra in LEGS:
            out = td / f"{leg}.o"
            # --allow-skipped-exports: a function the leg REFUSES must show up
            # below as a per-vector SYMBOL MISSING failure, not abort the leg.
            r = compile_leg(WAT, out, extra, allow_skip=True)
            if r.returncode != 0 or not out.exists():
                print(f"[{leg}] COMPILE FAILED: {(r.stdout + r.stderr)[-400:]}")
                bad += 1
                continue
            code, base, syms = load(out)
            for fn, args in CASES:
                if fn not in syms:
                    print(f"  [BUG] {leg:12} {fn}: SYMBOL MISSING (refused) x{len(args)}")
                    checks += len(args)
                    bad += len(args)
                    continue
                for a in args:
                    got, want = emulate(code, base, syms[fn], a), ref(fn, a)
                    checks += 1
                    ok = got == want
                    bad += not ok
                    shown = lambda v: v if isinstance(v, str) else f"0x{v:x}"
                    print(f"  [{'ok ' if ok else 'BUG'}] {leg:12} {fn}({'' if a is None else a}) "
                          f"-> {shown(got)} (wasmtime {shown(want)})")
            # the refusal
            pbe = td / "pbe.wat"
            pbe.write_text(PBE_WAT)
            r = compile_leg(pbe, td / f"pbe_{leg}.o", extra, allow_skip=True)
            hit = PBE_NEEDLE in (r.stdout + r.stderr)
            checks += 1
            bad += not hit
            print(f"  [{'ok ' if hit else 'BUG'}] {leg:12} pbe refused with the #1215 diagnostic: {hit}")
    print(f"#1215 CHECKS={checks - bad}/{checks}")
    if bad:
        print(f"RESULT: FAIL — {bad} divergence(s)")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
