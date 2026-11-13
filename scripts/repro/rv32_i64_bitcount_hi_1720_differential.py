#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 1752
"""#1720 — RV32: i64.clz/ctz/popcnt left a stale high word.

`(func (param $a i32) (result i64) local.get $a i64.extend_i32_u
   i64.const 0x100000000 i64.or i64.clz)` with a = 4 returned
0xc0de00010000001f on `-b riscv --target riscv32imac --relocatable` (the
harness's poisoned `a1`); wasmtime returns 0x1f.

ROOT CAUSE. The wasm result type of `i64.clz`, `i64.ctz` and `i64.popcnt` is
i64, but the RV32 selector's `lower_i64_clz` / `lower_i64_ctz` /
`lower_i64_popcnt` pushed an i32-typed value-stack entry (`push_i32`). The
function epilogue moves whatever the value-stack top is into the return
registers by ITS type, so an i32 entry wrote `a0` only and the caller read a
stale `a1` as the high word — silent wrong code. Any other consumer
(`i64.add`, `i64.store`, an i64 `local.set`, an i64 block result) popped it
with `pop_i64` and the function declined on a type mismatch. The fix pushes the
pair `(count, 0)` through one helper, `push_i64_zero_hi`, which
`i64.extend_i32_u` now shares — the high word is written by the op itself.

THE CLASS, MEASURED (not assumed). Every RV32 op that computes an i64-typed
result from one word (so that the high word is the op's own obligation) is
graded against wasmtime in every consumer shape below:

  i64.clz / i64.ctz / i64.popcnt         — the class (pushed i32 for an i64)
  i64.extend_i32_u / i64.extend_i32_s,
  i64.extend8_s / extend16_s / extend32_s — siblings (high word = 0 / sign)
  i64.eqz, i32.wrap_i64                   — i32-result controls (correctly
                                            i32; widened explicitly)

Consumer shapes: `ret` (the op's result is the function result — the silent
shape), `add` (an i64.add consumer), `local` (i64 local.set/get), `store`
(i64.store + i64.load round trip), `block` (an i64 block result), `pend` (an
i64 pending below the operand, folded with xor), `select` (an i64 select arm).
Every other RV32 i64 lowering pushes a result of its wasm type (audited by
reading every `push_i32`/`push_i64` site in selector.rs: the i64 compares and
eqz and wrap are i32 in wasm; add/sub/mul/bitwise/shift/rotate/div/rem/
extend*/load/const/global/local/call/select push pairs).

Each export takes two i32 params `(a, b)` that build the i64 operand
`a | b << 32`; `b` lands in `a1`, so a high word left unwritten reads back as
`b` — nonzero on most vectors. Every vector is executed under unicorn
(UC_ARCH_RISCV / UC_MODE_RISCV32, a0:a1 result) and compared to wasmtime. A
decline is a FAIL.

ARM CONTROL. The same module is compiled for cortex-m4 and cortex-m7dp
(`--relocatable`) and run under unicorn Thumb against the same wasmtime truth:
it proves the fixtures are right where the backend has no such defect. It needs
no linker while the ARM object's `.text` carries no relocation; if it ever
does, the ARM leg FAILS loudly instead of running unrelocated bytes.

Symbols come from the ELF `.symtab`, never `synth disasm` text.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/rv32_i64_bitcount_hi_1720_differential.py
"""

import os
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from elftools.elf.relocation import RelocationSection
from unicorn import UC_ARCH_ARM, UC_ARCH_RISCV, UC_MODE_RISCV32, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as ac
from unicorn import riscv_const as rc

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000
M32, M64 = 0xFFFFFFFF, 0xFFFFFFFFFFFFFFFF

# name -> (wasm result type, op text). The operand is always one i64.
OPS = {
    "i64_clz": ("i64", "i64.clz"),
    "i64_ctz": ("i64", "i64.ctz"),
    "i64_popcnt": ("i64", "i64.popcnt"),
    # Siblings: i64 result whose high word the op writes itself.
    "i64_ext_u": ("i64", "i32.wrap_i64 i64.extend_i32_u"),
    "i64_ext_s": ("i64", "i32.wrap_i64 i64.extend_i32_s"),
    "i64_ext8s": ("i64", "i64.extend8_s"),
    "i64_ext16s": ("i64", "i64.extend16_s"),
    "i64_ext32s": ("i64", "i64.extend32_s"),
    # i32-result controls, widened explicitly.
    "i64_eqz": ("i32", "i64.eqz"),
    "i32_wrap": ("i32", "i32.wrap_i64"),
}
CLASS = {"i64_clz", "i64_ctz", "i64_popcnt"}

OPERAND = ("local.get $a i64.extend_i32_u local.get $b i64.extend_i32_u "
           "i64.const 32 i64.shl i64.or")
PEND = "local.get $a i64.extend_i32_s i64.const 0x0F1E2D3C4B5A6978 i64.add"


def value(op):
    rkind, text = OPS[op]
    v = f"{OPERAND} {text}"
    return v + (" i64.extend_i32_u" if rkind == "i32" else "")


# shape -> wat body producing the i64 function result from `value(op)`.
SHAPES = {
    "ret": lambda v: v,
    "add": lambda v: f"{v} i64.const 0x0123456789ABCDEF i64.add",
    "local": lambda v: f"{v} local.set $r i64.const 3 drop local.get $r",
    "store": lambda v: f"i32.const 16 {v} i64.store i32.const 16 i64.load",
    "block": lambda v: f"(block (result i64) {v})",
    "pend": lambda v: f"{PEND} {v} i64.xor",
    "select": lambda v: f"{v} i64.const 0x7777777777777777 local.get $a select",
}


def func_wat(op, shape):
    return (f'(func (export "{op}__{shape}") (param $a i32) (param $b i32) (result i64)'
            f" (local $r i64)\n  {SHAPES[shape](value(op))})")


# The issue's module verbatim (its single param is `a`; `b` is unused there).
ISSUE = {
    "issue_clz": "i64.clz", "issue_ctz": "i64.ctz", "issue_popcnt": "i64.popcnt",
}


def issue_wat(name, opt):
    return (f'(func (export "{name}") (param $a i32) (param $b i32) (result i64)\n'
            f"  local.get $a i64.extend_i32_u i64.const 0x100000000 i64.or {opt})")


NAMES = list(ISSUE) + [f"{op}__{sh}" for op in OPS for sh in SHAPES]

# (a, b): b is the operand's high word AND what a stale `a1` reads back as.
VECTORS = [
    (4, 1), (0, 0), (0, 0x80000000), (0xFFFFFFFF, 0xFFFFFFFF),
    (0x80000000, 0), (1, 0xC0DE0001), (0x00F0F0F0, 0x12345678), (0, 1),
]


def module_wat():
    funcs = [issue_wat(n, o) for n, o in ISSUE.items()]
    funcs += [func_wat(op, sh) for op in OPS for sh in SHAPES]
    return "(module (memory 1)\n" + "\n".join(funcs) + ")\n"


def compile_obj(wat_path, out, target_args):
    cmd = [SYNTH, "compile", wat_path, "-o", out, *target_args, "--all-exports",
           "--relocatable", "--allow-skipped-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr)


def load(elf):
    with open(elf, "rb") as fh:
        ef = ELFFile(fh)
        text_idx = ef.get_section_index(".text")
        code = ef.get_section_by_name(".text").data()
        relocs = 0
        for sec in ef.iter_sections():
            if isinstance(sec, RelocationSection) and sec["sh_info"] == text_idx:
                relocs += sec.num_relocations()
        syms = {s.name: s["st_value"] for s in ef.get_section_by_name(".symtab").iter_symbols()
                if s.name and s["st_shndx"] == text_idx and s["st_info"]["type"] == "STT_FUNC"}
    return code, syms, relocs


def run_rv32(code, faddr, a, b):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, (len(code) + 0xFFFF) & ~0xFFFF)
    mu.mem_map(LIN, 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(rc.UC_RISCV_REG_SP, STK)
    mu.reg_write(rc.UC_RISCV_REG_S11, LIN)
    mu.reg_write(rc.UC_RISCV_REG_A0, a & M32)
    mu.reg_write(rc.UC_RISCV_REG_A1, b & M32)
    mu.reg_write(rc.UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + faddr, RET, count=200_000)
    except UcError as e:
        return f"ERR:{e}"
    if mu.reg_read(rc.UC_RISCV_REG_PC) != RET:
        return "ERR:did not return"
    return (mu.reg_read(rc.UC_RISCV_REG_A0) & M32) | ((mu.reg_read(rc.UC_RISCV_REG_A1) & M32) << 32)


def run_arm(code, faddr, a, b):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, (len(code) + 0xFFFF) & ~0xFFFF)
    mu.mem_map(LIN, 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(ac.UC_ARM_REG_SP, STK)
    mu.reg_write(ac.UC_ARM_REG_R11, LIN)
    mu.reg_write(ac.UC_ARM_REG_R10, 0x10000)
    mu.reg_write(ac.UC_ARM_REG_R0, a & M32)
    mu.reg_write(ac.UC_ARM_REG_R1, b & M32)
    mu.reg_write(ac.UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + (faddr & ~1)) | 1, RET, count=200_000)
    except UcError as e:
        return f"ERR:{e}"
    if mu.reg_read(ac.UC_ARM_REG_PC) & ~1 != RET:
        return "ERR:did not return"
    return (mu.reg_read(ac.UC_ARM_REG_R0) & M32) | ((mu.reg_read(ac.UC_ARM_REG_R1) & M32) << 32)


LEGS = [
    ("rv32", ["-b", "riscv", "--target", "riscv32imac"], run_rv32),
    ("cortex-m4", ["--target", "cortex-m4"], run_arm),
    ("cortex-m7dp", ["--target", "cortex-m7dp"], run_arm),
]


def op_of(n):
    return {"issue_clz": "i64_clz", "issue_ctz": "i64_ctz",
            "issue_popcnt": "i64_popcnt"}.get(n, n.split("__")[0])


def main():
    wat = module_wat()
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
    truth = {}
    for n in NAMES:
        f = inst.exports(store)[n]
        for a, b in VECTORS:
            truth[(n, a, b)] = f(store, a, b) & M64

    total_fail = 0
    executed = 0
    expected = 0
    with tempfile.TemporaryDirectory() as td:
        wat_path = os.path.join(td, "m.wat")
        with open(wat_path, "w") as fh:
            fh.write(wat)
        for leg, targs, runner in LEGS:
            obj = os.path.join(td, f"{leg}.o")
            rcode, log = compile_obj(wat_path, obj, targs)
            if rcode != 0 or not os.path.exists(obj):
                print(f"[{leg}] FAIL: compile rc={rcode}\n{log[-2000:]}")
                total_fail += 1
                continue
            code, syms, relocs = load(obj)
            if relocs:
                print(f"[{leg}] FAIL: .text carries {relocs} relocation(s); raw-load "
                      "execution would run unrelocated bytes")
                total_fail += 1
                continue
            wrong, declined = {}, []
            for n in NAMES:
                expected += len(VECTORS)
                if n not in syms:
                    declined.append(n)
                    continue
                for a, b in VECTORS:
                    got = runner(code, syms[n], a, b)
                    executed += 1
                    want = truth[(n, a, b)]
                    if got != want:
                        wrong.setdefault(n, []).append((a, b, got, want))
            cls = sorted(n for n in wrong if op_of(n) in CLASS)
            sib = sorted(n for n in wrong if op_of(n) not in CLASS)
            dcls = sum(op_of(n) in CLASS for n in declined)
            nwrong = sum(len(v) for v in wrong.values())
            print(f"[{leg}] exports={len(NAMES)} declined={len(declined)} "
                  f"(class={dcls} siblings={len(declined) - dcls}) "
                  f"wrong_vectors={nwrong} wrong_exports={len(wrong)} "
                  f"(class={len(cls)} siblings={len(sib)})")
            for n in declined:
                print(f"  DECLINED {n}")
            for n in cls + sib:
                a, b, got, want = wrong[n][0]
                g = f"0x{got:016x}" if isinstance(got, int) else got
                print(f"  WRONG {n}({a:#x}, {b:#x}) = {g}  wasmtime=0x{want:016x}"
                      f"  [{len(wrong[n])}/{len(VECTORS)} vectors]")
            total_fail += len(declined) + nwrong

    print(f"\n#1720 EMULATIONS={executed}/{expected}")
    if executed != expected:
        print(f"FAIL: only {executed} of {expected} vectors reached the emulator")
        total_fail += 1
    print("RV32 i64 bit-count high-word #1720 ORACLE: PASS" if not total_fail
          else f"RV32 i64 bit-count high-word #1720 ORACLE: FAIL ({total_fail})")
    sys.exit(1 if total_fail else 0)


if __name__ == "__main__":
    main()
