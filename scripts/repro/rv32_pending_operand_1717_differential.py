#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 1396
"""#1717 — RV32: a value still pending on the wasm stack is lost across an i64 div/rem.

`(module (func (export "f") (result i64)
   i64.const 5 i64.const 7 i64.const 2 i64.div_u i64.add))`
returned 6 on `-b riscv --target riscv32imac --relocatable`; wasmtime returns 8.

ROOT CAUSE. RV32 lowers all four i64 div/rem ops to an inline 64-iteration
long-division loop (`emit_i64_udiv_inline`, selector.rs) that runs on a FIXED
register file — `t0..t6` for its state and `s1..s3` for loop scratch — and
bypasses the allocator. Every other lowering asks `alloc_temp`, which skips the
registers pinned by live value-stack entries (#226). The core did not. So any
value BELOW the divide's two operands — a pending i32 or i64 that the allocator
had placed in one of those ten registers — was overwritten by the loop, and the
consumer read the quotient/remainder/counter state instead of the value. #317
had already seen the same core clobber the signed path's OWN sign masks and
fixed that one consumer by allocating them outside the core set; the values the
op does not own were never protected. The fix makes the core preserve every
live register it writes: each is stored to a frame slot before the core and
reloaded after it, on the same straight-line path, so the rule holds for any
depth, any type and inside any control frame.

A SECOND defect of the same seam surfaced once the first was fixed: copying the
core's result out of its fixed registers wrote `lo` first, and the allocator
can hand out the core's own `src_hi` register as `lo` — the high word of the
remainder was overwritten before it was read. Measured with ONLY the
preservation fix: 12 wrong vectors over 3 exports (`i64_rem_u__p32`,
`__p32_64`, `__p64_32`). `copy_div_result` now orders the two copies.

THE CLASS, MEASURED (not assumed). Every op below runs with nothing pending
(control) and with pending values at depth 1 and depth 2, of both i32 and i64
kinds, in both orders, plus two shapes where the op runs inside an `if` arm
with two values pending outside the frame:

  i64 div_s / div_u / rem_s / rem_u   — the fixed-register core (the class)
  i64 mul, shl/shr_s/shr_u, rotl/rotr, add/sub/and, compares, eqz,
      extend8/16/32_s, wrap, store+load round trip
  i32 div_s / div_u / rem_s / rem_u   — the #232 guard path
  i32 mul, shl/shr_s, lt_s

On the pre-fix compiler ONLY the four i64 div/rem ops go wrong (108 wrong
vectors over 27 exports, the issue's own module and the hand-written `br_if`
and loop shapes among them); every sibling,
the #232 i32 div/rem guard included, executes correctly and is graded here so a
regression elsewhere cannot hide behind this fix. Ops RV32 cannot lower in ANY
shape are not in the matrix (i32 clz/ctz/popcnt/rotl decline as unsupported;
i64 clz/ctz/popcnt push an i32-typed result, so the consumer declines on a
type mismatch). "Pending values ABOVE the operands" have no stack-machine form:
the operands are the top of the stack when the op runs. The closest shape — a
`br_if` value still held in an open frame's canonical register — is covered by
`live_regs`, which includes the open frames' `br_results`.

Each export takes two i32 params and returns i64 (RV32 declines i64 params,
#518), folding the op result and every pending value into one i64 so a clobber
of ANY of them changes the answer. Every vector is executed under unicorn
(UC_ARCH_RISCV / UC_MODE_RISCV32, ILP32, a0:a1 result) and compared to
wasmtime. A decline is a FAIL unless it is listed in `EXPECTED_RV32_DECLINES`
with its reason.

ARM CONTROL. The class's exports are also compiled for cortex-m4 and
cortex-m7dp (`--relocatable`) and run under unicorn Thumb against the same
wasmtime truth: the reporter saw ARM correct on this shape, and the control
proves the fixtures are not wrong themselves. It needs no linker while the ARM
object's `.text` carries no relocation; if it ever does, the ARM leg FAILS
loudly instead of running unrelocated bytes.

Symbols come from the ELF `.symtab`, never `synth disasm` text.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/rv32_pending_operand_1717_differential.py
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

# ── the op matrix ────────────────────────────────────────────────────────────
# name -> (operand kind, result kind, wat body that consumes the operands).
# Operand kinds: "i64bin" (two i64 from a, b), "i64sh" (i64 value, i64 shift
# amount from b), "i64un" (one i64), "i32bin", "i32un".
OPS = {
    # The fixed-register long-division core — the class #1717 belongs to.
    "i64_div_s": ("i64bin", "i64", "i64.div_s"),
    "i64_div_u": ("i64bin", "i64", "i64.div_u"),
    "i64_rem_s": ("i64bin", "i64", "i64.rem_s"),
    "i64_rem_u": ("i64bin", "i64", "i64.rem_u"),
    # Siblings: multi-instruction i64 expansions that allocate through
    # alloc_temp. Pinned MATCH.
    "i64_mul": ("i64bin", "i64", "i64.mul"),
    "i64_add": ("i64bin", "i64", "i64.add"),
    "i64_sub": ("i64bin", "i64", "i64.sub"),
    "i64_and": ("i64bin", "i64", "i64.and"),
    "i64_shl": ("i64sh", "i64", "i64.shl"),
    "i64_shr_s": ("i64sh", "i64", "i64.shr_s"),
    "i64_shr_u": ("i64sh", "i64", "i64.shr_u"),
    "i64_rotl": ("i64sh", "i64", "i64.rotl"),
    "i64_rotr": ("i64sh", "i64", "i64.rotr"),
    "i64_eq": ("i64bin", "i32", "i64.eq"),
    "i64_lt_s": ("i64bin", "i32", "i64.lt_s"),
    "i64_lt_u": ("i64bin", "i32", "i64.lt_u"),
    "i64_ge_s": ("i64bin", "i32", "i64.ge_s"),
    "i64_gt_u": ("i64bin", "i32", "i64.gt_u"),
    "i64_eqz": ("i64un", "i32", "i64.eqz"),
    "i64_ext8s": ("i64un", "i64", "i64.extend8_s"),
    "i64_ext16s": ("i64un", "i64", "i64.extend16_s"),
    "i64_ext32s": ("i64un", "i64", "i64.extend32_s"),
    "i32_wrap": ("i64un", "i32", "i32.wrap_i64"),
    "i64_memrt": ("i64un", "i64",
                  "local.set $t i32.const 16 local.get $t i64.store "
                  "i32.const 16 i64.load"),
    # i32 div/rem: the #232 overflow-guard path (hardware div, guard temps).
    "i32_div_s": ("i32bin", "i32", "i32.div_s"),
    "i32_div_u": ("i32bin", "i32", "i32.div_u"),
    "i32_rem_s": ("i32bin", "i32", "i32.rem_s"),
    "i32_rem_u": ("i32bin", "i32", "i32.rem_u"),
    "i32_mul": ("i32bin", "i32", "i32.mul"),
    "i32_shl": ("i32bin", "i32", "i32.shl"),
    "i32_shr_s": ("i32bin", "i32", "i32.shr_s"),
    "i32_lt_s": ("i32bin", "i32", "i32.lt_s"),
}
CLASS = {"i64_div_s", "i64_div_u", "i64_rem_s", "i64_rem_u"}

# Pending-value shapes, bottom of the stack first. "" is the no-pending control.
SHAPES = {
    "none": [],
    "p32": ["i32"],
    "p64": ["i64"],
    "p32_32": ["i32", "i32"],
    "p32_64": ["i32", "i64"],
    "p64_32": ["i64", "i32"],
    "p64_64": ["i64", "i64"],
}
# The op inside an `if` arm, with two values of one width pending OUTSIDE the
# frame. These fold on the stack, never through locals: the shared
# `infer_i64_locals` heuristic mis-types a local set after an `if (result)`
# (RV32 declines it loudly), which would hide the shape this exists to run.
IF_SHAPES = {"if_p64_64": "i64", "if_p32_32": "i32"}
ALL_SHAPES = list(SHAPES) + list(IF_SHAPES)

# (a, b) vectors. b is never 0 and (a, b) is never (INT_MIN, -1) for i32, and
# the i64 operand built from a is never INT64_MIN, so no vector traps.
VECTORS = [(1000003, 7), (-123456789, 13), (5, -3), (0x7FFF1234, 37)]


def pend_wat(kind, k):
    """A pending value that depends on param a, so it lives in an allocated
    register (not a constant the backend could rematerialize)."""
    if kind == "i32":
        return f"local.get $a i32.const {0x13579BDF + 0x101 * k} i32.add"
    return (f"local.get $a i64.extend_i32_s i64.const {0x0F1E2D3C4B5A6978 + 0x10001 * k} "
            "i64.add")


def operands_wat(okind):
    lhs64 = "local.get $a i64.extend_i32_s i64.const 0x0123456700000000 i64.xor"
    if okind == "i64bin":
        return f"{lhs64} local.get $b i64.extend_i32_s"
    if okind == "i64sh":
        return f"{lhs64} local.get $b i64.extend_i32_u"
    if okind == "i64un":
        return lhs64
    if okind == "i32bin":
        return "local.get $a local.get $b"
    return "local.get $a"


def func_wat(op, shape):
    okind, rkind, body = OPS[op]
    head = f'(func (export "{op}__{shape}") (param $a i32) (param $b i32) (result i64)'
    core = f"{operands_wat(okind)} {body}"
    if shape in IF_SHAPES:
        w = IF_SHAPES[shape]
        # Bring the op's result to the frame's width inside the arm.
        conv = {("i32", "i64"): " i64.extend_i32_u", ("i64", "i32"): " i32.wrap_i64"}
        core += conv.get((rkind, w), "")
        if w == "i64":
            fold = "i64.xor i64.const 17 i64.rotl i64.xor"
        else:
            fold = "i32.xor i32.const 31 i32.mul i32.xor i64.extend_i32_u"
        return "\n".join([
            head, "  (local $t i64)",
            "  " + pend_wat(w, 0), "  " + pend_wat(w, 1),
            f"  local.get $b (if (result {w}) (then {core}) (else {w}.const 99))",
            f"  {fold})"])
    pend = SHAPES[shape]
    # Every local is set exactly once with a value of its declared type and
    # read only after that set: the folds below never read an unset local.
    decl = [f"(local $r {rkind})", "(local $t i64)"]
    decl += [f"(local $p{k} {kind})" for k, kind in enumerate(pend)]
    lines = [head, "  " + " ".join(decl)]
    for k, kind in enumerate(pend):
        lines.append("  " + pend_wat(kind, k))
    lines.append("  " + core)
    lines.append("  local.set $r")
    for k in reversed(range(len(pend))):
        lines.append(f"  local.set $p{k}")
    # Fold: every value lands in a different bit position (rotations 0, 17,
    # 41), so a clobber of any one of them changes the result.
    ext = lambda kind: " i64.extend_i32_u" if kind == "i32" else ""  # noqa: E731
    fold = f"local.get $r{ext(rkind)}"
    for k, kind in enumerate(pend):
        fold += f" local.get $p{k}{ext(kind)} i64.const {17 + 24 * k} i64.rotl i64.xor"
    lines.append(f"  {fold})")
    return "\n".join(lines)


# Hand-written class shapes, run on every leg with the matrix:
#   issue_1717 — the issue's module verbatim apart from the (unused) params
#                every export here takes: `5 + 7/2`, wasmtime 8, pre-fix RV32 6.
#   brif_1717  — the pending value is a `br_if` operand of an open block: it
#                stays on the stack on the fall-through edge into the divide.
#   loop_1717  — the accumulator pending across an i64.rem_u in a loop body.
EXTRA_WAT = {
    "issue_1717": ('(func (export "issue_1717") (param $a i32) (param $b i32) (result i64)\n'
                   "  i64.const 5 i64.const 7 i64.const 2 i64.div_u i64.add)"),
    "brif_1717": ('(func (export "brif_1717") (param $a i32) (param $b i32) (result i64)\n'
                  "  (block $B (result i64)\n"
                  "    local.get $a i64.extend_i32_u i64.const 1000 i64.add\n"
                  "    local.get $b i32.eqz br_if $B\n"
                  "    local.get $a i64.extend_i32_u local.get $b i64.extend_i32_u i64.div_u\n"
                  "    i64.add))"),
    "loop_1717": ('(func (export "loop_1717") (param $a i32) (param $b i32) (result i64)\n'
                  "  (local $i i32) (local $acc i64)\n"
                  "  (loop $L\n"
                  "    local.get $acc local.get $a i64.extend_i32_u i64.const 3 i64.add\n"
                  "    local.get $b i64.extend_i32_u i64.rem_u i64.add local.set $acc\n"
                  "    local.get $i i32.const 1 i32.add local.tee $i i32.const 5 i32.lt_u br_if $L)\n"
                  "  local.get $acc)"),
}


def module_wat():
    funcs = list(EXTRA_WAT.values()) + [func_wat(op, sh) for op in OPS for sh in ALL_SHAPES]
    return "(module (memory 1)\n" + "\n".join(funcs) + ")\n"


def compile_obj(wat_path, out, target_args):
    cmd = [SYNTH, "compile", wat_path, "-o", out, *target_args, "--all-exports", "--relocatable", "--allow-skipped-exports"]
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


# (leg, compile args, runner, ops run on the leg). The ARM legs run the #1717
# class only: they are the control that the fixtures are right where the
# reporter saw ARM correct. ARM's OWN pending-value defects (i32 div_s/rem_s/
# rem_u with a value pending below — the #1715 family) are out of this
# oracle's subject and would make an RV32 gate red for an ARM reason.
LEGS = [
    ("rv32", ["-b", "riscv", "--target", "riscv32imac"], run_rv32, set(OPS) | set(EXTRA_WAT)),
    # brif_1717 is not on the ARM legs: ARM's direct selector declines it
    # loudly ("#509: an i64 value carried over a br/br_if/br_table is not yet
    # supported by the direct selector").
    ("cortex-m4", ["--target", "cortex-m4"], run_arm, CLASS | {"issue_1717", "loop_1717"}),
    ("cortex-m7dp", ["--target", "cortex-m7dp"], run_arm, CLASS | {"issue_1717", "loop_1717"}),
]

# RV32 exports that decline LOUDLY today, each with its reason. A decline is
# reach, not silent wrongness: it is allowed only when listed here, and a
# listed export that starts compiling is executed and graded like any other
# (it is reported, not failed). Every one is register-pool exhaustion — the
# selector's #226 loud skip, surfaced as `unsupported ... Select` — at the
# deepest pending shapes; none is caused by the #1717 fix (the pre-fix
# compiler declines exactly the same 18).
EXPECTED_RV32_DECLINES = {
    # i64 div_s/rem_s: the |x| expansion's five temps per operand on top of
    # the pending values and the two sign masks.
    "i64_div_s__p32_64", "i64_div_s__p64_32", "i64_div_s__p64_64",
    "i64_div_s__if_p64_64",
    "i64_rem_s__p32_64", "i64_rem_s__p64_32", "i64_rem_s__p64_64",
    "i64_rem_s__if_p64_64",
    # i64 mul / rotl / rotr: their own expansions' pressure.
    "i64_mul__p64_64", "i64_mul__if_p64_64",
    "i64_rotl__p32_64", "i64_rotl__p64_32", "i64_rotl__p64_64",
    "i64_rotl__if_p64_64",
    "i64_rotr__p32_64", "i64_rotr__p64_32", "i64_rotr__p64_64",
    "i64_rotr__if_p64_64",
}


def main():
    wat = module_wat()
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, wat)
    names = list(EXTRA_WAT) + [f"{op}__{sh}" for op in OPS for sh in ALL_SHAPES]
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    truth = {}
    for n in names:
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
        for leg, targs, runner, ops in LEGS:
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
            wrong, declined, allowed, now_compiles = {}, [], [], []
            for n in names:
                if n not in ops and n.split("__")[0] not in ops:
                    continue
                listed = leg == "rv32" and n in EXPECTED_RV32_DECLINES
                if n not in syms:
                    (allowed if listed else declined).append(n)
                    continue
                if listed:
                    now_compiles.append(n)
                expected += len(VECTORS)
                for a, b in VECTORS:
                    got = runner(code, syms[n], a, b)
                    executed += 1
                    want = truth[(n, a, b)]
                    if got != want:
                        wrong.setdefault(n, []).append((a, b, got, want))
            op_of = lambda n: "i64_div_u" if n in EXTRA_WAT else n.split("__")[0]  # noqa: E731
            cls = sorted(n for n in wrong if op_of(n) in CLASS)
            sib = sorted(n for n in wrong if op_of(n) not in CLASS)
            nwrong = sum(len(v) for v in wrong.values())
            print(f"[{leg}] exports={sum(n in ops or n.split('__')[0] in ops for n in names)} "
                  f"declined={len(declined)} listed_declines={len(allowed)} "
                  f"wrong_vectors={nwrong} wrong_exports={len(wrong)} "
                  f"(class={len(cls)} siblings={len(sib)})")
            for n in declined:
                print(f"  DECLINED (unlisted) {n}")
            for n in now_compiles:
                print(f"  NOW COMPILES (listed decline, executed and graded) {n}")
            for n in cls + sib:
                a, b, got, want = wrong[n][0]
                g = f"0x{got:016x}" if isinstance(got, int) else got
                print(f"  WRONG {n}({a}, {b}) = {g}  wasmtime=0x{want:016x}"
                      f"  [{len(wrong[n])}/{len(VECTORS)} vectors]")
            total_fail += len(declined) + nwrong

    print(f"\n#1717 EMULATIONS={executed}/{expected}")
    if executed != expected:
        print(f"FAIL: only {executed} of {expected} vectors reached the emulator")
        total_fail += 1
    print("RV32 pending-operand #1717 ORACLE: PASS" if not total_fail
          else f"RV32 pending-operand #1717 ORACLE: FAIL ({total_fail})")
    sys.exit(1 if total_fail else 0)


if __name__ == "__main__":
    main()
