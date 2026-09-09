#!/usr/bin/env python3
# One-shot generator for the committed
# scripts/repro/home_alias_class_1189_*.wat modules; the oracle that executes them is
# scripts/repro/home_alias_class_1189_differential.py. Re-run only to regenerate them.
"""RQ-65-ALIASCLASS (#1189) — generate the per-consumer-family modules.

Every function takes params HOMED IN R0..R3 (AAPCS, call-free) — or, in the
`promo` module, a non-param i32 local that the direct selector PROMOTES into
r4 — feeds them to ONE consumer op, then RE-READS every home and folds it into
the result, so a consumer that wrote a home in place is observable as a wrong
answer, not a lucky one. The shapes are the operand families of the direct
selector's op loop: i32/i64 binary + compare + unary, conversions, loads and
stores (home as address AND as value), select (home as arm and as
condition), function-level `br_if` with a home value, `br_table` on a home
index, if-with-params (RQ-64-MVLOWER), local/global set of a home value,
bulk memory with home operands (#677), the get→set→use WAR (#989).

The generator is the case table's twin: a family is added HERE, committed as
.wat, and picked up by both the execution oracle (vectors in its CASES) and
the corpus audit sweep (which globs scripts/repro/*.wat).
"""

from pathlib import Path

HERE = Path(__file__).parent / "repro"

I32_BIN = ["add", "sub", "mul", "div_s", "div_u", "rem_s", "rem_u", "and",
           "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr"]
I32_CMP = ["eq", "ne", "lt_s", "lt_u", "le_s", "le_u", "gt_s", "gt_u",
           "ge_s", "ge_u"]
I32_UN = ["eqz", "clz", "ctz", "popcnt", "extend8_s", "extend16_s"]
I64_BIN = I32_BIN
I64_CMP = I32_CMP
I64_UN = ["eqz", "clz", "ctz", "popcnt", "extend8_s", "extend16_s",
          "extend32_s"]
LOADS = ["i32.load", "i32.load8_u", "i32.load8_s", "i32.load16_u",
         "i32.load16_s"]
STORES = ["i32.store", "i32.store8", "i32.store16"]
LOADS64 = ["i64.load", "i64.load8_u", "i64.load8_s", "i64.load16_u",
           "i64.load16_s", "i64.load32_u", "i64.load32_s"]
STORES64 = ["i64.store", "i64.store8", "i64.store16", "i64.store32"]


def i32_module():
    fns = []
    # binary: OP(a,b) + a + b  — params a=r0, b=r1
    for op in I32_BIN:
        fns.append(f'''  (func (export "b_{op}") (param i32 i32) (result i32)
    (i32.add (i32.add (i32.{op} (local.get 0) (local.get 1)) (local.get 0)) (local.get 1)))''')
    # binary with the homes in r2/r3 (a 4-param function; p0/p1 are dead)
    for op in ["add", "sub", "xor", "shl"]:
        fns.append(f'''  (func (export "hi_{op}") (param i32 i32 i32 i32) (result i32)
    (i32.add (i32.add (i32.{op} (local.get 2) (local.get 3)) (local.get 2)) (local.get 3)))''')
    for op in I32_CMP:
        fns.append(f'''  (func (export "c_{op}") (param i32 i32) (result i32)
    (i32.add (i32.add (i32.mul (i32.{op} (local.get 0) (local.get 1)) (i32.const 100)) (local.get 0)) (local.get 1)))''')
    for op in I32_UN:
        fns.append(f'''  (func (export "u_{op}") (param i32) (result i32)
    (i32.add (i32.mul (i32.{op} (local.get 0)) (i32.const 1000)) (local.get 0)))''')
    # unary on the same home twice (both operands alias one register)
    fns.append('''  (func (export "same_twice") (param i32) (result i32)
    (i32.add (i32.sub (local.get 0) (local.get 0)) (local.get 0)))''')
    # select: home as then-arm, else-arm, condition
    fns.append('''  (func (export "sel_then") (param i32 i32) (result i32)
    (i32.add (i32.add (select (local.get 0) (i32.const 77) (local.get 1)) (local.get 0)) (local.get 1)))''')
    fns.append('''  (func (export "sel_else") (param i32 i32) (result i32)
    (i32.add (i32.add (select (i32.const 77) (local.get 0) (local.get 1)) (local.get 0)) (local.get 1)))''')
    fns.append('''  (func (export "sel_cond") (param i32 i32) (result i32)
    (i32.add (i32.add (select (i32.const 5) (i32.const 9) (local.get 0)) (local.get 0)) (local.get 1)))''')
    # function-level br_if carrying a home value; fall-through re-reads both
    fns.append('''  (func (export "brif_fn") (param i32 i32) (result i32)
    (local.get 1) (local.get 0) (br_if 0) (drop)
    (i32.add (local.get 0) (local.get 1)))''')
    # br_if into a value-carrying block with a home value, home re-read after
    fns.append('''  (func (export "brif_blk") (param i32 i32) (result i32)
    (i32.add (block (result i32) (local.get 1) (local.get 0) (br_if 0) (drop) (i32.const 3))
             (i32.add (local.get 0) (local.get 1))))''')
    # br_table on a home index, home re-read after
    fns.append('''  (func (export "brtab") (param i32 i32) (result i32)
    (block (block (block (local.get 0) (br_table 0 1 2))
        (return (i32.add (local.get 0) (i32.const 100))))
      (return (i32.add (local.get 0) (i32.const 200))))
    (i32.add (local.get 0) (local.get 1)))''')
    # if with a block PARAM that is a home (RQ-64-MVLOWER), then-arm empty
    fns.append('''  (func (export "ifparam") (param i32 i32) (result i32)
    (local.get 0)
    (if (param i32) (result i32) (local.get 1) (then) (else (drop) (i32.const 7)))
    (local.get 0) (i32.add) (local.get 1) (i32.add))''')
    # block whose fall-through result is a home, home re-read after (#509)
    fns.append('''  (func (export "blkfall") (param i32 i32) (result i32)
    (i32.add (block (result i32) (local.get 0)) (i32.add (local.get 0) (local.get 1))))''')
    # loop result + param-bounded count (#663 shape)
    fns.append('''  (func (export "loopcnt") (param i32 i32) (result i32)
    (local i32)
    (block (loop
      (br_if 1 (i32.ge_u (local.get 2) (local.get 0)))
      (local.set 2 (i32.add (local.get 2) (i32.const 1)))
      (br 0)))
    (i32.add (i32.add (local.get 2) (local.get 0)) (local.get 1)))''')
    # local.set / local.tee of ANOTHER local with a home value
    fns.append('''  (func (export "set_other") (param i32 i32) (result i32)
    (local i32)
    (local.set 2 (local.get 0))
    (local.set 2 (i32.add (local.get 2) (i32.const 1)))
    (i32.add (i32.add (local.get 2) (local.get 0)) (local.get 1)))''')
    fns.append('''  (func (export "tee_other") (param i32 i32) (result i32)
    (local i32)
    (i32.add (i32.add (local.tee 2 (local.get 0)) (local.get 0)) (i32.add (local.get 2) (local.get 1))))''')
    # get -> set -> use (#989 WAR)
    fns.append('''  (func (export "war_set") (param i32 i32) (result i32)
    (local.get 0)
    (local.set 0 (i32.const 200))
    (i32.add (local.get 0)) (i32.add (local.get 1)))''')
    # loads with a home as the address, stores with a home as address / value
    for op in LOADS:
        n = op.replace(".", "_")
        fns.append(f'''  (func (export "ld_{n}") (param i32 i32) (result i32)
    (i32.add (i32.add ({op} (local.get 0)) (local.get 0)) (local.get 1)))''')
    for op in STORES:
        n = op.replace(".", "_")
        fns.append(f'''  (func (export "st_{n}") (param i32 i32) (result i32)
    ({op} (local.get 0) (local.get 1))
    (i32.add (i32.add (i32.load (local.get 0)) (local.get 0)) (local.get 1)))''')
    # bulk memory with home operands (#677): dst/val/len then re-read all
    fns.append('''  (func (export "fill") (param i32 i32 i32) (result i32)
    (memory.fill (local.get 0) (local.get 1) (local.get 2))
    (i32.add (i32.add (i32.add (i32.load8_u (local.get 0)) (local.get 0)) (local.get 1)) (local.get 2)))''')
    fns.append('''  (func (export "copy") (param i32 i32 i32) (result i32)
    (memory.copy (local.get 0) (local.get 1) (local.get 2))
    (i32.add (i32.add (i32.add (i32.load8_u (local.get 0)) (local.get 0)) (local.get 1)) (local.get 2)))''')
    body = "\n".join(fns)
    return f'''(module
  (memory (export "memory") 1)
{body})
'''


def i64_module():
    fns = []
    for op in I64_BIN:
        fns.append(f'''  (func (export "b_{op}") (param i64 i64) (result i64)
    (i64.add (i64.add (i64.{op} (local.get 0) (local.get 1)) (local.get 0)) (local.get 1)))''')
    for op in I64_CMP:
        fns.append(f'''  (func (export "c_{op}") (param i64 i64) (result i64)
    (i64.add (i64.add (i64.mul (i64.extend_i32_u (i64.{op} (local.get 0) (local.get 1))) (i64.const 100)) (local.get 0)) (local.get 1)))''')
    for op in I64_UN:
        if op == "eqz":
            fns.append('''  (func (export "u_eqz") (param i64) (result i64)
    (i64.add (i64.mul (i64.extend_i32_u (i64.eqz (local.get 0))) (i64.const 1000)) (local.get 0)))''')
        else:
            fns.append(f'''  (func (export "u_{op}") (param i64) (result i64)
    (i64.add (i64.mul (i64.{op} (local.get 0)) (i64.const 1000)) (local.get 0)))''')
    # conversions across widths
    fns.append('''  (func (export "wrap") (param i64 i64) (result i64)
    (i64.add (i64.add (i64.extend_i32_u (i32.wrap_i64 (local.get 0))) (local.get 0)) (local.get 1)))''')
    fns.append('''  (func (export "ext_s") (param i32 i32) (result i64)
    (i64.add (i64.mul (i64.extend_i32_s (local.get 0)) (i64.const 1000)) (i64.extend_i32_u (i32.add (local.get 0) (local.get 1)))))''')
    fns.append('''  (func (export "ext_u") (param i32 i32) (result i64)
    (i64.add (i64.mul (i64.extend_i32_u (local.get 0)) (i64.const 1000)) (i64.extend_i32_u (i32.add (local.get 0) (local.get 1)))))''')
    # i64 select with home arms / i32 cond
    fns.append('''  (func (export "sel64") (param i64 i64) (result i64)
    (i64.add (i64.add (select (local.get 0) (i64.const 77) (i32.wrap_i64 (local.get 1))) (local.get 0)) (local.get 1)))''')
    # i64 loads / stores with an i32 address param and i64 value param
    for op in LOADS64:
        n = op.replace(".", "_")
        fns.append(f'''  (func (export "ld_{n}") (param i32 i64) (result i64)
    (i64.add (i64.add ({op} (local.get 0)) (i64.extend_i32_u (local.get 0))) (local.get 1)))''')
    for op in STORES64:
        n = op.replace(".", "_")
        fns.append(f'''  (func (export "st_{n}") (param i32 i64) (result i64)
    ({op} (local.get 0) (local.get 1))
    (i64.add (i64.add (i64.load (local.get 0)) (i64.extend_i32_u (local.get 0))) (local.get 1)))''')
    # get -> set -> use on an i64 pair (#989, both halves)
    fns.append('''  (func (export "war64") (param i64 i64) (result i64)
    (local.get 0)
    (local.set 0 (i64.const 0x300000004))
    (i64.add (local.get 0)) (i64.add (local.get 1)))''')
    body = "\n".join(fns)
    return f'''(module
  (memory (export "memory") 1)
{body})
'''


def promo_module():
    """A non-param i32 local, written before read, >=2 depth-0 accesses: the
    direct selector promotes it into r4 (#390) and RV32 into s8 (#472), and
    `local.get` of it aliases the promoted register uncopied."""
    fns = []
    for op in ["add", "sub", "mul", "shl", "xor", "div_u"]:
        fns.append(f'''  (func (export "p_{op}") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (i32.add (i32.add (i32.{op} (local.get 1) (local.get 0)) (local.get 1)) (local.get 1)))''')
    fns.append('''  (func (export "p_sel") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (i32.add (select (local.get 1) (i32.const 77) (local.get 0)) (local.get 1)))''')
    fns.append('''  (func (export "p_store") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (i32.store (i32.const 64) (local.get 1))
    (i32.add (i32.load (i32.const 64)) (local.get 1)))''')
    fns.append('''  (func (export "p_war") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (local.get 1)
    (local.set 1 (i32.const 200))
    (i32.add (local.get 1)))''')
    fns.append('''  (func (export "p_fill") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (memory.fill (i32.const 64) (local.get 1) (local.get 1))
    (i32.add (i32.load8_u (i32.const 64)) (local.get 1)))''')
    fns.append('''  (func (export "p_brif") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (local.get 1) (local.get 0) (br_if 0) (drop)
    (i32.add (local.get 1) (i32.const 1)))''')
    body = "\n".join(fns)
    return f'''(module
  (memory (export "memory") 1)
{body})
'''


def main():
    (HERE / "home_alias_class_1189_i32.wat").write_text(i32_module())
    (HERE / "home_alias_class_1189_i64.wat").write_text(i64_module())
    (HERE / "home_alias_class_1189_promo.wat").write_text(promo_module())
    print("wrote 3 modules")


if __name__ == "__main__":
    main()
