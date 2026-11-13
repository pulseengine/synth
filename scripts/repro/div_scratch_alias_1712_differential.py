#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 9000
"""#1712 — ARM direct selector: a div/rem/rotl SCRATCH register lands on one
of the op's own already-POPPED operands.

THE DEFECT. `select_with_stack` pops an op's operands off the virtual stack
and then allocates. The allocator's reservation is "registers held by the
vstack" plus `live_params` (params read again LATER). A popped operand is on
neither list: it has left the vstack, and if it is a param whose last
`local.get` fed this op, it is already dead in `live_params`. Allocating the
DESTINATION after the pops is fine — it is written last. But four lowerings
allocate a SCRATCH that is written BEFORE the operands are read again:

    i32.div_s  INT_MIN/-1 guard: MOVW/MOVT tmp, 0x80000000; CMP dividend, tmp;
               CMN divisor, #1; SDIV dst, dividend, divisor
    i32.rem_s  SDIV tmp, dividend, divisor; MLS dst, tmp, divisor, dividend
    i32.rem_u  UDIV tmp, dividend, divisor; MLS dst, tmp, divisor, dividend
    i32.rotl   RSB  tmp, amount, #32;      ROR dst, value, tmp

The round-robin allocator hands out the popped register whenever its cursor
happens to sit there. The issue's shape (a nested block/br_if/if/br) merely
moved the cursor onto r1, the divisor, so the guard loaded INT_MIN into the
divisor and every div_s returned `x / INT_MIN` = 0:

    32: movw r1, #0 ; 36: movt r1, #0x8000 ; ... ; 46: sdiv r0, r0, r1

rem_s/rem_u produce a wrong remainder the same way; rotl's Rocq rule carries
the `rs <> rn` side condition, so its instance was a LOUD decline (the export
was skipped), never wrong code. The RV32 selector has reserved the operands
for exactly this guard since #232 (`alloc_temp_avoiding(&[rs1, rs2])`); the
ARM direct selector never got the port. The optimized path (`ir_to_arm`) is
not affected: it uses R12 for these scratches and allocates `rd` avoiding
`[rn, rm]`. i32.div_u's reciprocal-multiply path already reserved them.

THE POPULATION. The cursor position is the whole trigger, so every class op
is compiled at EVERY cursor offset (k = 0..9 dropped constants advance the
9-register round-robin by k), as a mid-expression op and as the function's
last op (dst forced to r0), with param operands, temp operands, and constant
divisors; plus a DEEP-stack leg (d live temps below the operands, so the
cursor has to wrap past them onto the popped temps), the issue's own module,
and contrast ops that must stay correct (div_u, shl, rotr, mul). Every export
runs on cortex-m4 AND cortex-m7dp, `--relocatable` (the direct selector) and
self-contained. The pre-fix binary is RED here (wrong vectors across the
class ops and a skipped rotl export); the fix is GREEN.

A wasm trap must be a unicorn fault (UDF) and vice versa; a fault where
wasmtime returned is a FAILURE.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/div_scratch_alias_1712_differential.py
"""
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as ac

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
TARGETS = ["cortex-m4", "cortex-m7dp"]
M32 = 0xFFFFFFFF
CODE, LIN, STK = 0x100000, 0x40000, 0x80000
RET = CODE + 0xF0000
INSNS = 200_000
R_ARM_THM_CALL, R_ARM_THM_JUMP24 = 10, 30

CLASS = ["div_s", "rem_s", "rem_u", "rotl"]
CONTRAST = ["div_u", "shl", "rotr", "mul"]
CONSTS = [7, -7, 3, 10, 16, -1, 2, 0x10001]

# Includes INT_MIN/-1 (the overflow trap), x/0 (the zero trap), and the
# issue's own vectors.
VEC2 = [(7, 2), (9, 3), (100, 7), (-100, 7), (0x7FFFFFFF, 5), (-1, 3),
        (12345, -17), (5, 31), (-0x80000000, -1), (-0x80000000, 3), (5, 0)]

# Floors on vectors actually COMPARED, per leg. A run that compiled an empty
# module or skipped everything must not pass.
MIN_COMPARED_PER_LEG = 2000

emulations = 0


def die(msg):
    print(f"#1712 DIV-SCRATCH ORACLE: FAIL — {msg}")
    sys.exit(1)


def build_module():
    funcs = []  # (name, nparams, body)

    def add(name, n, body):
        funcs.append((name, n, body))

    pre = lambda k: "(drop (i32.const 1)) " * k  # noqa: E731
    for k in range(10):
        for op in CLASS + CONTRAST:
            add(f"{op}_mid_k{k}", 2,
                f"{pre(k)}(i32.add (i32.{op} (local.get 0) (local.get 1)) (i32.const 3))")
            add(f"{op}_last_k{k}", 2, f"{pre(k)}(i32.{op} (local.get 0) (local.get 1))")
            add(f"{op}_tmp_k{k}", 2,
                f"{pre(k)}(i32.add (i32.{op} (i32.add (local.get 0) (i32.const 1)) "
                f"(i32.sub (local.get 1) (i32.const 1))) (i32.const 3))")
        for op in ("div_s", "rem_s", "rem_u"):
            for c in CONSTS:
                add(f"{op}_c{c & M32:x}_k{k}", 2,
                    f"{pre(k)}(i32.add (i32.{op} (local.get 0) (i32.const {c})) (local.get 1))")
    # DEEP stack: d live temps under two temp operands; summed afterwards so
    # every one of them is read after the op.
    for d in range(8):
        for op in CLASS + ["div_u"]:
            below = " ".join(f"(i32.add (local.get 0) (i32.const {j + 1}))" for j in range(d))
            tail = "(i32.add) " * d
            add(f"{op}_deep{d}", 2,
                f"{below} (i32.{op} (i32.add (local.get 0) (i32.const 11)) "
                f"(i32.sub (local.get 1) (i32.const 1))) {tail}")
    # The issue's module (#1712), and its class siblings in the div_s slot.
    for op in CLASS + ["div_u"]:
        add(f"issue_{op}", 2, f"""
  (block $outer (result i32)
   (block $inner (result i32)
    i32.const 10 local.get 0 i32.eqz br_if $inner drop
    local.get 0 i32.const 0 i32.lt_s
    if i32.const -1 br $outer end
    local.get 0 local.get 1 i32.{op} br $outer)
   i32.const 100 i32.add)""")
    # #1716's two modules, same class: the div_s INT_MIN temp landed on the
    # dividend after an early `return` (b4a: `movt r0,#0x8000; cmp r0,r0`),
    # and the rem_s quotient temp on the dividend after a `br_if` (b4b:
    # `sdiv r0,r0,r7; mls r8,r0,r7,r0`).
    add("issue1716_b4a", 2, """
  i32.const 0 if i32.const 0 return end
  local.get 1 i32.const -1 i32.eq if i32.const 0 local.get 0 i32.sub return end
  local.get 0 local.get 1 i32.div_s""")
    add("issue1716_b4b", 2, """
  block (result i32) local.get 0 local.get 1 i32.div_s local.get 1 i32.const 1
  i32.and br_if 0 drop local.get 0 i32.const 7 i32.rem_s end""")
    # #1715, same class: three constant-divisor div/rem terms in one
    # expression; a rem quotient temp landed on a popped operand.
    add("issue1715_b3", 1, """
  local.get 0 i32.const 3 i32.div_s local.get 0 i32.const 5 i32.rem_u i32.add
  local.get 0 i32.const 9 i32.rem_s i32.add""")
    wat = "(module\n" + "\n".join(
        f' (func (export "{n}") ' + "(param i32) " * p + f"(result i32) {b})"
        for n, p, b in funcs) + ")\n"
    return funcs, wat


def encode_thm_bl(pc, target):
    off = (target - (pc + 4)) & 0x01FFFFFF
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return (0xF000 | (s << 10) | ((off >> 12) & 0x3FF),
            0xD000 | (j1 << 13) | (j2 << 11) | ((off >> 1) & 0x7FF))


def load(path):
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] for s in st.iter_symbols() if s.name}
        sec = e.get_section_by_name(".text")
        if sec is None:
            die("no .text section")
        base = sec["sh_addr"]
        text = bytearray(sec.data())
        for rel in e.iter_sections():
            if rel["sh_type"] != "SHT_REL" or rel.name != ".rel.text":
                continue
            for r in rel.iter_relocations():
                name = st.get_symbol(r["r_info_sym"]).name
                if r["r_info_type"] not in (R_ARM_THM_CALL, R_ARM_THM_JUMP24):
                    die(f"unexpected reloc type {r['r_info_type']} against {name!r}")
                if name not in syms:
                    die(f"reloc names {name!r}, not a defined symbol")
                hw = encode_thm_bl(CODE + r["r_offset"], CODE + ((syms[name] - base) & ~1))
                text[r["r_offset"]:r["r_offset"] + 4] = (
                    hw[0].to_bytes(2, "little") + hw[1].to_bytes(2, "little"))
    return syms, bytes(text), base


def run(syms, text, base, name, args):
    global emulations
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STK, 0x10000)
    mu.mem_write(CODE, text)
    mu.reg_write(ac.UC_ARM_REG_SP, STK + 0xC000)
    mu.reg_write(ac.UC_ARM_REG_R11, LIN)
    mu.reg_write(ac.UC_ARM_REG_R10, 0x10000)
    regs = [ac.UC_ARM_REG_R0, ac.UC_ARM_REG_R1, ac.UC_ARM_REG_R2, ac.UC_ARM_REG_R3]
    for i, rr in enumerate(regs):
        mu.reg_write(rr, (args[i] & M32) if i < len(args) else 0xFEEDFACE)
    mu.reg_write(ac.UC_ARM_REG_LR, RET | 1)
    emulations += 1
    try:
        mu.emu_start((CODE + ((syms[name] - base) & ~1)) | 1, RET, count=INSNS)
    except UcError as ex:
        return f"fault:{ex}"
    if mu.reg_read(ac.UC_ARM_REG_PC) & ~1 != RET & ~1:
        return "budget"
    return mu.reg_read(ac.UC_ARM_REG_R0) & M32


def leg(engine, module, funcs, obj, label):
    syms, text, base = load(obj)
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = inst.exports(store)
    checks = fails = 0
    bad_names = set()
    for name, nparams, _ in funcs:
        if name not in syms:
            fails += 1
            bad_names.add(name)
            print(f"BUG [{label}] {name}: export missing from the object")
            continue
        for v in VEC2:
            args = list(v[:nparams])
            try:
                want = exports[name](store, *args) & M32
            except wasmtime.Trap:
                want = "trap"
            got = run(syms, text, base, name, args)
            if isinstance(got, str) and got.startswith("fault:") and want == "trap":
                got = "trap"  # UDF #0/#1 is synth's trap
            checks += 1
            if got != want:
                fails += 1
                bad_names.add(name)
                if fails <= 60:
                    print(f"BUG [{label}] {name}{tuple(args)}: want={want} got={got}")
    ops = sorted({n.split("_k")[0].split("_deep")[0] for n in bad_names})
    print(f"[{label}] {checks - fails}/{checks} vectors match wasmtime; "
          f"{len(bad_names)} wrong exports; shapes: {ops}")
    return checks, fails


def main():
    funcs, wat = build_module()
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, wat)
    total = total_fail = 0
    with tempfile.TemporaryDirectory() as td:
        wat_path = Path(td) / "div_scratch_1712.wat"
        wat_path.write_text(wat)
        for target in TARGETS:
            for label, reloc in (("relocatable", True), ("self-contained", False)):
                obj = os.path.join(td, f"{target}_{label}.o")
                p_cmd = [SYNTH, "compile", str(wat_path), "-t", target, "--all-exports",
                         "--allow-skipped-exports", "-o", obj]
                if reloc:
                    p_cmd.append("--relocatable")
                p = subprocess.run(p_cmd, capture_output=True, text=True)
                if p.returncode != 0:
                    die(f"compile failed ({target}/{label}):\n{p.stderr[-1500:]}")
                c, f = leg(engine, module, funcs, obj, f"{target}:{label}")
                if c < MIN_COMPARED_PER_LEG:
                    print(f"FAIL floor [{target}:{label}]: {c} compared < {MIN_COMPARED_PER_LEG}")
                    f += 1
                total += c
                total_fail += f
    print(f"\n#1712 CHECKS={total - total_fail}/{total} (emulations={emulations}, "
          f"exports={len(funcs)})")
    print("#1712 div/rem/rotl scratch-alias ORACLE: " + ("FAIL" if total_fail else "PASS"))
    sys.exit(1 if total_fail else 0)


if __name__ == "__main__":
    main()
