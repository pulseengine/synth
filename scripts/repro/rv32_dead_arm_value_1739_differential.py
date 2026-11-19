#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 602
"""#1739 — RV32 returned a dead if-arm's value.

On RV32 (`-b riscv --target riscv32imac --relocatable`), three exports of
`scripts/repro/if_arm_dead_value_1691.wat` compiled and returned the wrong
value: `t_i32_void_target(0)` returned 0xfffffffa where wasmtime returns 93,
and `t_i32_unreachable` and `t_i64_void_target` were wrong on most inputs. The
disassembly read the register of the arm whose value is dead. This is the RV32
counterpart of the ARM defect fixed for #1691; RV32 has its own selector.

ROOT CAUSE, two halves.

1. A `br` carried the whole operand-stack delta above its target's entry
   height. The RV32 selector never saw the decoder's blocktype table, so a
   `br 1` to a VOID block from inside an if, with `i32.const 1` on the stack,
   made that `1` the void block's "result": the block's `end` pushed it and
   the `i32.sub` after the block read it in place of the `100` beneath. The
   same over-count hit `br_if` to a void block or to a loop. The fix threads
   `CompileConfig::current_func_block_arity` into the selector: a branch
   carries exactly its target's declared arity (block/if: results; loop:
   params) and the values beneath are unwound.
2. Only `return` ended the reachable region (#882). After `br`, `br_table` and
   `unreachable` the dead tail was lowered as if live, so an else-less if's
   `end` handed the dead then-arm's leftovers to the code after the if
   (`t_i32_unreachable`), and dead code that popped below the arm's entry
   height was declined as a stack underflow (`refuse_below`) or tripped the
   #343 arm-arity check (`ctl_i32_arity_held`). The fix enters the same
   dead-code walk after those transfers (after `br` only when the target's
   arity is known — a join reached by branch edges alone then publishes the
   edges' values, so their count must be the declared one).

A third defect of the same join, found while measuring this one and silent on
main: an if/else whose then-arm FALLS THROUGH and that is also the target of a
value-carrying branch. The then-arm jumped to the join with its value in its
own register, and the branch edge in another, and the join read the branch's
(`z_live`, `z_dead`, `z_then_br` below: x=1 returns 99, wasmtime 94). The fix
makes the then-arm's registers canonical for such a join (branch from the else
arm) or moves the then-arm's results into the branch's registers before its
`jal` (branch from inside the then arm).

LEGS (every leg pins its EXACT compiled set; a decline of a pinned export is a
FAIL, and so is an unexpected compile):

  1691        the #1691 fixture, `--all-exports`. Pinned declines: the
              value-carrying `br_table` (#509) and every f32/f64 export
              (RV32 has no float lowering).
  1691-func   the issue's three exports, one `--func-name` compile each — the
              CLI per-function path, which threads the blocktype table on its
              own.
  extra       shapes of the same class beyond the fixture, embedded below.
  corpus      every corpus export whose RV32 bytes this fix moved and that has
              an i32/i64 signature, plus those it newly compiles — the moved
              bytes owe execution evidence (dead code is no longer emitted).

Each compiled export is called for every x in VECTORS under unicorn RV32
(a0, or a1:a0 for i64) against wasmtime; a trap must be a trap on both sides.
`refuse_below` and `ctl_i32_arity_held` compile on RV32 since this fix and are
graded like every other export.

Symbols come from the ELF `.symtab`, never `synth disasm` text.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/rv32_dead_arm_value_1739_differential.py
"""

import os
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from elftools.elf.relocation import RelocationSection
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn import riscv_const as rc

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
HERE = os.path.dirname(os.path.abspath(__file__))
CODE, LIN, STK, RET = 0x100000, 0x400000, 0x90000, 0x200000
M32, M64 = 0xFFFFFFFF, 0xFFFFFFFFFFFFFFFF
VECTORS = [0, 1, 2, 4, 5, 7, 100, 0x80000000, 0xFFFFFFFF]
RV = ["-b", "riscv", "--target", "riscv32imac", "--relocatable"]
# `t_i32_loop_exit` counts up to x + 3: x = 0x80000000 is two billion
# iterations, past the emulator's instruction budget, so it is not run there.
SKIP_VECTORS = {"t_i32_loop_exit": {0x80000000}}
BUDGET = 500_000

FIXTURE_1691 = os.path.join(HERE, "if_arm_dead_value_1691.wat")
TARGETS = ["t_i32_void_target", "t_i32_unreachable", "t_i64_void_target"]
# Exports of the #1691 fixture that must DECLINE on RV32, with the reason.
DECLINES_1691 = {
    "t_i32_br_table": "value-carrying br_table (#509)",
    **{n: "no RV32 float lowering" for n in (
        "t_f32_then", "t_f32_else", "t_f32_both", "t_f32_nested",
        "t_f32_br_table", "t_f32_unreachable", "t_f32_void_target",
        "t_f64_void_target", "t_f64_beneath_f32_carried")},
}

EXTRA_WAT = """(module
  (func (export "x_brif_void_extra") (param i32) (result i32)
    i32.const 100
    block
      i32.const 5
      local.get 0
      br_if 0
      drop
    end
    i32.const 7
    i32.sub)
  (func (export "x_brif_void_extra_i64") (param i32) (result i64)
    i64.const 100
    block
      i64.const 5
      local.get 0
      br_if 0
      drop
    end
    i64.const 7
    i64.sub)
  (func (export "x_br_dead_tail") (param i32) (result i32)
    i32.const 100
    block (result i32)
      i32.const 3
      br 0
      i32.const 4
      i32.add
    end
    i32.sub)
  (func (export "x_loop_brif_extra") (param i32) (result i32) (local i32)
    i32.const 100
    loop
      local.get 1
      i32.const 1
      i32.add
      local.tee 1
      local.get 1
      i32.const 3
      i32.lt_u
      br_if 0
      drop
    end
    local.get 1
    i32.sub)
  (func (export "x_block_brif_carry") (param i32) (result i32)
    i32.const 100
    block (result i32)
      i32.const 9
      i32.const 5
      local.get 0
      br_if 0
      i32.add
    end
    i32.sub)
  (func (export "x_else_unreachable") (param i32) (result i32)
    i32.const 100
    local.get 0
    if (result i32)
      i32.const 5
    else
      unreachable
    end
    i32.sub)
  (func (export "x_else_brif_then_live") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.const 1
    i32.and
    if (result i32)
      i32.const 11
    else
      i32.const 22
      local.get 0
      i32.const 4
      i32.and
      br_if 0
      drop
      i32.const 33
    end
    i32.sub)
  (func (export "z_live") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.const 1
    i32.and
    if (result i32)
      i32.const 1
      i32.const 2
      i32.const 3
      i32.add
      i32.add
    else
      i32.const 22
      local.get 0
      i32.const 4
      i32.and
      br_if 0
      drop
      i32.const 33
    end
    i32.sub)
  (func (export "z_dead") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.const 1
    i32.and
    if (result i32)
      i32.const 1
      i32.const 2
      i32.const 3
      i32.add
      i32.add
    else
      i32.const 22
      local.get 0
      i32.const 4
      i32.and
      br_if 0
      unreachable
    end
    i32.sub)
  (func (export "z_then_br") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.const 1
    i32.and
    if (result i32)
      i32.const 22
      local.get 0
      i32.const 4
      i32.and
      br_if 0
      drop
      i32.const 1
      i32.const 2
      i32.const 3
      i32.add
      i32.add
    else
      i32.const 33
    end
    i32.sub)
  (func (export "z_live_i64") (param i32) (result i64)
    i64.const 100
    local.get 0
    i32.const 1
    i32.and
    if (result i64)
      i64.const 1
      i64.const 2
      i64.const 3
      i64.add
      i64.add
    else
      i64.const 22
      local.get 0
      i32.const 4
      i32.and
      br_if 0
      drop
      i64.const 33
    end
    i64.sub)
  (func (export "g3") (param i32) (result i32)
    block (result i32)
      i32.const 11
      local.get 0 i32.const 1 i32.and
      br_if 0
      i32.const 33
      local.get 0 i32.const 2 i32.and
      br_if 0
      i32.add
    end)
  (func (export "k1") (param i32) (result i32)
    block (result i32)
      i32.const 5
      i32.const 11
      local.get 0 i32.const 1 i32.and
      br_if 0
      i32.const 33
      local.get 0 i32.const 2 i32.and
      br_if 0
      drop
      i32.add
    end)
  (func (export "k2") (param i32) (result i32)
    block (result i32 i32)
      i32.const 5
      i32.const 11
      i32.const 22
      local.get 0 i32.const 1 i32.and
      br_if 0
      drop
    end
    i32.const 8 i32.shl i32.or)
  (func (export "k4") (param i32) (result i32)
    block (result i32)
      block
        i32.const 11
        local.get 0 i32.const 1 i32.and
        br_if 1
        i32.const 33
        local.get 0 i32.const 2 i32.and
        br_if 1
        i32.add
        local.set 0
      end
      local.get 0
    end)
  (func (export "k5") (param i32) (result i64)
    block (result i64)
      i64.const 5
      i64.const 0x1100000011
      local.get 0 i32.const 1 i32.and
      br_if 0
      i64.const 0x3300000033
      local.get 0 i32.const 2 i32.and
      br_if 0
      drop
      i64.add
    end)
  (func (export "g2") (param i32) (result i32)
    i32.const 1000
    local.get 0 i32.const 1 i32.and
    if (result i32)
      i32.const 5
      i32.const 11
      local.get 0 i32.const 2 i32.and
      br_if 0
      i32.const 33
      local.get 0 i32.const 4 i32.and
      br_if 0
      drop
      i32.add
    else
      i32.const 9
    end
    i32.sub)
  (func (export "f3") (param i32) (result i64)
    i64.const 0x7000000000
    local.get 0 i32.const 1 i32.and
    if (result i64)
      i64.const 0x100000001
      i64.const 0x200000002
      i64.add
    else
      i64.const 0x1600000016
      local.get 0 i32.const 4 i32.and
      br_if 0
      unreachable
    end
    i64.sub)
  (func (export "h1") (param i32) (result i32) (local i32)
    i32.const 100
    block
      block
        local.get 0
        br_table 0 1 0
        drop drop
        i32.const 5 local.set 1
      end
      i32.const 1
      local.set 1
    end
    local.get 1
    i32.sub)
  (func (export "c1") (param i32) (result i32)
    i32.const 1000
    block (result i32 i32)
      i32.const 11
      i32.const 22
      local.get 0 i32.const 1 i32.and
      br_if 0
      drop drop
      i32.const 3
      i32.const 44
    end
    i32.sub i32.sub)
  (func (export "c4") (param i32) (result i32)
    block (result i32 i32)
      i32.const 1
      i32.const 2
      local.get 0 i32.const 1 i32.and
      br_if 0
      i32.const 10 i32.add
      local.set 0
      i32.const 20 i32.add
      local.get 0
      local.get 0 i32.const 3 i32.sub
      local.get 0 i32.const 100 i32.gt_u
      br_if 0
      drop
    end
    i32.const 16 i32.shl i32.or)
  (func (export "m_ifelse_edges") (param i32) (result i32)
    i32.const 1000
    local.get 0 i32.const 1 i32.and
    if (result i32 i32)
      i32.const 1
      i32.const 2
    else
      i32.const 3
      i32.const 4
      local.get 0 i32.const 2 i32.and
      br_if 0
      i32.const 5
      local.get 0 i32.const 4 i32.and
      br_if 0
      drop
      drop
      drop
      i32.const 9
      i32.const 8
    end
    i32.const 16 i32.shl i32.or
    i32.sub)
  (func (export "perm_ifelse_select") (param i32) (result i32)
    local.get 0 i32.const 1 i32.and
    if (result i32 i32)
      i32.const 1
      i32.const 2
    else
      i32.const 30
      i32.const 40
      local.get 0 i32.const 2 i32.and
      select
      i32.const 50
    end
    i32.const 16 i32.shl i32.or)
  (func (export "perm_ifelse_64") (param i32) (result i64)
    local.get 0 i32.const 1 i32.and
    if (result i64 i64)
      i64.const 0x100000002
      i64.const 0x300000004
    else
      i64.const 30
      i64.const 40
      i64.sub
      i64.const 0x5000000060
    end
    i64.const 3 i64.mul i64.add)
  (func (export "perm_ifelse_mixed") (param i32) (result i64)
    local.get 0 i32.const 1 i32.and
    if (result i64 i32)
      i64.const 0x100000002
      i32.const 4
    else
      i32.const 30
      i32.const 40
      i32.sub
      i64.extend_i32_s
      i32.const 50
    end
    i64.extend_i32_u i64.add)
  (func (export "d_live_below_if") (param i32) (result i32)
    block (result i32)
      i32.const 6
      local.get 0 i32.const 1 i32.and
      br_if 0
      local.get 0 i32.const 2 i32.and
      if
        i32.const 7
        local.get 0 i32.const 4 i32.and
        br_if 1
        drop
      end
    end)
  (func (export "m_two_edges_permuted") (param i32) (result i32)
    block (result i32 i32)
      i32.const 7
      i32.const 1
      i32.const 2
      local.get 0 i32.const 1 i32.and
      br_if 0
      local.get 0 i32.const 2 i32.and
      br_if 0
      drop
    end
    i32.const 16 i32.shl i32.or)
)
"""

# Exports of EXTRA_WAT that must DECLINE on RV32. `d_live_below_if`: the
# block's first `br_if` donates its operand's register as the block's result
# register, and that operand is still live beneath the inner `if` when the
# second edge must write the same register. Renaming it on that path would
# leave the if's other path reading the old register, so the edge declines.
# (The previous revision of this fix compiled it and returned 7 for x=2,
# wasmtime 6.)
EXTRA_DECLINES = {
    "d_live_below_if": "join register live below the inner if's entry (#1739)",
}

# (fixture, export): the corpus exports whose RV32 bytes this fix moves, or
# that it newly compiles, with an i32/i64 signature and no imports. Measured
# by an --all-exports .text comparison of every scripts/repro fixture against
# main 265235dc. Non-exported functions that moved (gust_kernel func_4/func_5,
# k_mutex_unlock func_7/func_9) lost only a dead trailing epilogue.
CORPUS = [
    ("aarch64_cf_538.wat", "always_br"),
    ("aarch64_cf_538.wat", "nested_brif1"),
    ("aarch64_ctrlflow_851.wat", "isqrt_ceil"),
    ("br_value_509.wat", "pick_br"),
    ("branch_boundary_930.wat", "br"),
    ("brvalue_operand_1215.wat", "br.nested-br_table-value-index"),
    ("brvalue_operand_1215.wat", "br_if.nested-br-value"),
    ("brvalue_operand_1215.wat", "labels.switch"),
    ("brvalue_operand_1215.wat", "prop_block"),
    ("brvalue_operand_1215.wat", "prop_loop"),
    ("brvalue_operand_1215.wat", "prop_return"),
    ("brvalue_operand_1215.wat", "prop_unreachable"),
    ("brvalue_operand_1215.wat", "repro931.carried"),
    ("brvalue_operand_1215.wat", "repro931.promoted"),
    ("ra003_switch_1230.wat", "switch"),
    ("rv32_br_value_931.wat", "br64"),
    ("rv32_br_value_931.wat", "carried"),
    ("rv32_br_value_931.wat", "computed"),
    ("rv32_br_value_931.wat", "promoted"),
    ("rv32_br_value_931.wat", "simple"),
    ("unreachable_665.wat", "boom"),
    ("unreachable_665.wat", "guarded"),
]

ENGINE = wasmtime.Engine()


def compile_obj(src, out, extra):
    if os.path.exists(out):
        os.remove(out)
    r = subprocess.run([SYNTH, "compile", src, "-o", out, *RV, *extra],
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def load(elf):
    with open(elf, "rb") as fh:
        ef = ELFFile(fh)
        ti = ef.get_section_index(".text")
        code = ef.get_section_by_name(".text").data()
        relocs = sum(s.num_relocations() for s in ef.iter_sections()
                     if isinstance(s, RelocationSection) and s["sh_info"] == ti)
        syms = {s.name: s["st_value"] for s in ef.get_section_by_name(".symtab").iter_symbols()
                if s.name and s["st_shndx"] == ti and s["st_info"]["type"] == "STT_FUNC"}
    return code, syms, relocs


def run_rv32(code, faddr, args):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, (len(code) + 0xFFFF) & ~0xFFFF)
    mu.mem_map(LIN, 0x110000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(rc.UC_RISCV_REG_SP, STK)
    mu.reg_write(rc.UC_RISCV_REG_S11, LIN)
    mu.reg_write(rc.UC_RISCV_REG_RA, RET)
    # A stale a1 must not pass for an i64 high word.
    mu.reg_write(rc.UC_RISCV_REG_A1, 0xC0DE0001)
    for i, a in enumerate(args):
        mu.reg_write(rc.UC_RISCV_REG_A0 + i, a & M32)
    try:
        mu.emu_start(CODE + faddr, RET, count=BUDGET)
    except UcError:
        return "trap"
    if mu.reg_read(rc.UC_RISCV_REG_PC) != RET:
        # Stopped by the instruction budget, not by a fault: an outcome of
        # its own, which never equals a wasmtime result or trap.
        return "budget-overrun"
    return (mu.reg_read(rc.UC_RISCV_REG_A0) & M32) | ((mu.reg_read(rc.UC_RISCV_REG_A1) & M32) << 32)


def signature(module, name):
    for e in module.exports:
        if e.name == name:
            return [str(p) for p in e.type.params], [str(r) for r in e.type.results]
    raise SystemExit(f"FAIL: export {name!r} not in module")


def truth(module, name, x, nparams):
    store = wasmtime.Store(ENGINE)
    inst = wasmtime.Instance(store, module, [])
    s = x - (1 << 32) if x & 0x80000000 else x
    try:
        return inst.exports(store)[name](store, *([s] * nparams))
    except wasmtime.Trap:
        return "trap"


def grade(leg, module, code, syms, names):
    """Run every name for every vector; return (executed, wrong list)."""
    executed, wrong = 0, []
    for n in names:
        params, results = signature(module, n)
        if any(p != "i32" for p in params) or results not in (["i32"], ["i64"]):
            wrong.append((n, "ungraded signature", f"{params}->{results}", ""))
            continue
        for x in VECTORS:
            if x in SKIP_VECTORS.get(n, ()):
                continue
            want = truth(module, n, x, len(params))
            got = run_rv32(code, syms[n], [x] * len(params))
            executed += 1
            if want != "trap":
                want &= M64 if results == ["i64"] else M32
            if got != "trap" and results == ["i32"]:
                got &= M32
            if got != want:
                wrong.append((n, x, got, want))
    return executed, wrong


def report(leg, executed, compiled, wrong, set_errors):
    print(f"[{leg}] compiled={len(compiled)} executed={executed} wrong_vectors={len(wrong)} "
          f"wrong_exports={len({w[0] for w in wrong})} set_errors={len(set_errors)}")
    for e in set_errors:
        print(f"  {e}")
    seen = set()
    for n, x, got, want in wrong:
        if n in seen:
            continue
        seen.add(n)
        cnt = sum(1 for w in wrong if w[0] == n)
        g = f"{got:#x}" if isinstance(got, int) else got
        w = f"{want:#x}" if isinstance(want, int) else want
        print(f"  WRONG {n}(x={x:#x}) = {g}  wasmtime={w}  [{cnt} vector(s)]")
    return len(wrong) + len(set_errors)


def module_leg(leg, src, module, expect_declined, td):
    obj = os.path.join(td, f"{leg}.o")
    rcode, log = compile_obj(src, obj, ["--all-exports", "--allow-skipped-exports"])
    if rcode != 0 or not os.path.exists(obj):
        print(f"[{leg}] FAIL: compile rc={rcode}\n{log[-1500:]}")
        return 0, 1
    code, syms, relocs = load(obj)
    if relocs:
        print(f"[{leg}] FAIL: .text carries {relocs} relocation(s)")
        return 0, 1
    names = [e.name for e in module.exports]
    expect = [n for n in names if n not in expect_declined]
    errors = [f"DECLINED {n} (pinned to compile)" for n in expect if n not in syms]
    errors += [f"COMPILED {n} (pinned to decline: {expect_declined[n]})"
               for n in expect_declined if n in syms]
    graded = [n for n in expect if n in syms]
    executed, wrong = grade(leg, module, code, syms, graded)
    return executed, report(leg, executed, graded, wrong, errors)


def per_function_leg(leg, items, td):
    """One `--func-name` compile per (fixture, export); a decline is a FAIL."""
    executed_total, fails = 0, 0
    wrong_all, errors, compiled = [], [], []
    for fixture, name in items:
        module = wasmtime.Module.from_file(ENGINE, fixture)
        obj = os.path.join(td, "one.o")
        rcode, log = compile_obj(fixture, obj, ["--func-name", name])
        if rcode != 0 or not os.path.exists(obj):
            last = (log.strip().splitlines() or ["?"])[-1][:160]
            errors.append(f"DECLINED {os.path.basename(fixture)}:{name} :: {last}")
            continue
        code, syms, relocs = load(obj)
        if relocs or name not in syms:
            errors.append(f"UNGRADABLE {os.path.basename(fixture)}:{name} relocs={relocs}")
            continue
        compiled.append(name)
        executed, wrong = grade(leg, module, code, syms, [name])
        executed_total += executed
        wrong_all += wrong
    fails += report(leg, executed_total, compiled, wrong_all, errors)
    return executed_total, fails


def main():
    total, fails = 0, 0
    with tempfile.TemporaryDirectory() as td:
        m1691 = wasmtime.Module.from_file(ENGINE, FIXTURE_1691)
        e, f = module_leg("1691", FIXTURE_1691, m1691, DECLINES_1691, td)
        total += e
        fails += f

        e, f = per_function_leg("1691-func", [(FIXTURE_1691, n) for n in TARGETS], td)
        total += e
        fails += f

        extra = os.path.join(td, "extra_1739.wat")
        with open(extra, "w") as fh:
            fh.write(EXTRA_WAT)
        e, f = module_leg("extra", extra, wasmtime.Module(ENGINE, EXTRA_WAT), EXTRA_DECLINES, td)
        total += e
        fails += f

        e, f = per_function_leg("corpus", [(os.path.join(HERE, a), b) for a, b in CORPUS], td)
        total += e
        fails += f

    print(f"\n#1739 EMULATIONS={total}")
    print("RV32 dead if-arm value #1739 ORACLE: PASS" if not fails
          else f"RV32 dead if-arm value #1739 ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
