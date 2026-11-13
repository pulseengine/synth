#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 110000
"""#1721 — ARM: a value PENDING on the operand stack below a temp-using
expansion (i32/i64 div/rem, rotl/rotr, popcnt, clz/ctz, mul, the shifts)
must survive the expansion, and so must the op's own operands.

THE REPORT. With an i64 pending below an i32 `div_s` / `rem_u`, the ARM
direct selector (`--relocatable`, cortex-m4 and cortex-m7dp) returned a
wrong i64:

    div_s(1000003, 7): wasmtime 0x117434, synth 0xffffffffedc62199

THE MECHANISM — not the pending value. The issue read this as the pending
i64 being overwritten. The emitted code on main 34781a8c says otherwise: the
pending pair (r6:r7) is intact, and the div_s INT_MIN guard temp lands on
the division's own DIVIDEND, the popped param alias r0:

    movw r0, #0 ; movt r0, #0x8000 ; cmp r0, r0 ; ... ; sdiv r8, r0, r1

so the quotient is INT_MIN / divisor. rem_u's UDIV quotient temp lands on
the dividend the same way. That is the #1712 class: a scratch written
BEFORE the op's own popped operands are read again, allocated with only
`live_params` reserved. The pending i64 is merely what moved the
round-robin cursor onto r0. The #1712 fix (those four scratches reserve the
popped operands) closes it; nothing in the allocator's treatment of values
still ON the stack was wrong (`stack_live_regs` reserves both halves of an
i64 pair).

THE POPULATION, built to refute that verdict rather than assume it. Every
ARM expansion with internal temps or a multi-instruction sequence — i32
div_s/div_u/rem_s/rem_u/rotl/rotr/shl/shr_s/shr_u/mul/popcnt/clz/ctz and
all thirteen i64 twins — with a value pending BELOW its operands: an i32 and
an i64 at depth 1, i32-over-i64 / i32-over-i32 / i64-over-i64 at depth 2,
and a bare i32 or i64 param alias pending. Operands are popped param aliases
or computed temps. Three signatures: (i32, i32) -> i64 and (i64, i64) -> i64
take the direct selector on every leg; (i32, i32) -> i32 with i32 pending
values is what the self-contained build's OPTIMIZED path (ir_to_arm)
accepts, and that leg asserts it really lowered a floor of functions there.
The round-robin cursor is the trigger, so every shape is compiled at cursor
offsets k = 0..8 (dropped constants advance the 9-register round-robin).
Every pending value is read AFTER the op; i64 results compare both halves.
Every export runs on cortex-m4 AND cortex-m7dp, `--relocatable` and
self-contained, against wasmtime under unicorn. A wasm trap must be a UDF
fault and vice versa, and every export must compile: a decline is a failure
here (pre-#1712, i32.rotl's `rs <> rn` side condition turned the same
temp-on-operand instance into a loud skip).

MEASURED. main 34781a8c: RED — wrong i32 div_s/rem_s/rem_u values under
every pending shape whose operands are popped param aliases (plus the
i64-over-i64 temp-operand shape), the issue's two exports, and declined
i32.rotl exports; no wrong value in any other op. main + the #1712 fix:
GREEN, every shape, every leg, 0 declined.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/pending_below_temp_1721_differential.py
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
M64 = (1 << 64) - 1
CODE, LIN, STK = 0x100000, 0x40000, 0x80000
RET = CODE + 0xF0000
INSNS = 400_000
R_ARM_THM_CALL, R_ARM_THM_JUMP24 = 10, 30

# Two signature groups (AAPCS: an i64 takes an even register pair):
#   "w" (param $a i32) (param $b i32) (result i64): a=r0, b=r1. Every value is
#       computed into a register, so pressure stays inside the 9-register file.
#   "d" (param $x i64) (param $y i64) (result i64): x=r0:r1, y=r2:r3. Its
#       operands are popped i64 PARAM aliases (the i64 analogue of the issue's
#       `local.get $a` dividend).
#   "n" (param $a i32) (param $b i32) (result i32): i32 ops under i32 pending
#       values only, the shape the self-contained build's OPTIMIZED path
#       (ir_to_arm) accepts — the "w"/"d" groups fall back to the direct
#       selector there (i64 result / i64 param).
I32_BIN = ["div_s", "div_u", "rem_s", "rem_u", "rotl", "rotr", "shl", "shr_s",
           "shr_u", "mul"]
I32_UN = ["popcnt", "clz", "ctz"]
I64_BIN = ["div_s", "div_u", "rem_s", "rem_u", "rotl", "rotr", "shl", "shr_s",
           "shr_u", "mul"]
I64_UN = ["popcnt", "clz", "ctz"]
SIGS = {"w": (("i32", "i32"), "i64"), "d": (("i64", "i64"), "i64"),
        "n": (("i32", "i32"), "i32")}

# Vectors per signature. The issue's own two, signed/unsigned edges, a shift
# amount >= width, INT_MIN / -1 (the overflow trap) and a zero divisor (the
# zero trap).
VECS = {
    "w": [(1000003, 7), (100, 3), (-7, -2), (0x7FFFFFFF, 31), (-0x80000000, 33),
          (-0x80000000, -1), (5, 0)],
    "n": [(1000003, 7), (100, 3), (-7, -2), (0x7FFFFFFF, 31), (-0x80000000, 33),
          (-0x80000000, -1), (5, 0)],
    "d": [(123456789012, 7), (-5, 3), (0x7FFFFFFFFFFF, -2), (-1, 63),
          (-(1 << 63), -1), (1 << 40, 65), (5, 0)],
}

# A leg must EXECUTE at least this many vectors: a run that compiled an empty
# module or declined everything must not pass.
MIN_COMPARED_PER_LEG = 28000
# The self-contained build must lower at least this many functions on the
# optimized path (ir_to_arm). Measured 194 per self-contained leg: every "n"
# shape at k = 0 and some at k = 1, since the optimized path declines to the
# direct selector once the dropped constants exhaust its R4-R8 scratch pool
# (#496). The relocatable leg lowers 0 there by design (#197).
MIN_OPTIMIZED_SELF_CONTAINED = 194

emulations = 0

# Operand forms per signature. "p": popped param aliases (i32 in w; i64 in d).
# "t": computed temps.
OPERANDS = {
    ("w", 32, "p"): ("(local.get 0)", "(local.get 1)"),
    ("w", 32, "t"): ("(i32.add (local.get 0) (i32.const 1))",
                     "(i32.sub (local.get 1) (i32.const 1))"),
    ("w", 64, "t"): ("(i64.mul (i64.extend_i32_s (local.get 0)) (i64.const 0x100000003))",
                     "(i64.extend_i32_s (local.get 1))"),
    ("n", 32, "p"): ("(local.get 0)", "(local.get 1)"),
    ("n", 32, "t"): ("(i32.add (local.get 0) (i32.const 1))",
                     "(i32.sub (local.get 1) (i32.const 1))"),
    ("d", 64, "p"): ("(local.get 0)", "(local.get 1)"),
    ("d", 64, "t"): ("(i64.add (local.get 0) (i64.const 1))",
                     "(i64.sub (local.get 1) (i64.const 1))"),
    ("d", 32, "t"): ("(i32.wrap_i64 (local.get 0))", "(i32.wrap_i64 (local.get 1))"),
}
# Pending values (computed into registers, read after the op), and a bare
# param alias.
PENDING = {
    "w": {"p64": "(i64.add (i64.extend_i32_s (local.get 0)) (i64.const 1000))",
          "p64b": "(i64.extend_i32_u (i32.mul (local.get 1) (i32.const 3)))",
          "p32": "(i32.add (local.get 1) (i32.const 77))",
          "alias32": "(local.get 0)", "alias64": None},
    "n": {"p32": "(i32.add (local.get 1) (i32.const 77))",
          "p32b": "(i32.mul (local.get 0) (i32.const 3))",
          "alias32": "(local.get 0)"},
    "d": {"p64": "(i64.add (local.get 0) (i64.const 1000))",
          "p64b": "(i64.mul (local.get 1) (i64.const 3))",
          "p32": "(i32.wrap_i64 (i64.add (local.get 1) (i64.const 77)))",
          "alias32": None, "alias64": "(local.get 0)"},
}


def die(msg):
    print(f"#1721 PENDING-BELOW-TEMP ORACLE: FAIL — {msg}")
    sys.exit(1)


def op_expr(sig, width, op, form):
    x, y = OPERANDS[(sig, width, form)]
    un = I32_UN if width == 32 else I64_UN
    if op in un:
        return f"(i{width}.{op} {x})"
    return f"(i{width}.{op} {x} {y})"


def as64(expr, w):
    return expr if w == 64 else f"(i64.extend_i32_u {expr})"


def shapes_for(sig, e, w):
    """Each body leaves exactly one i64. The pending value is the FIRST
    operand of a folded s-expression, so it is pushed before — and sits below
    — the op's operands while the op's expansion runs, and is read after."""
    P = PENDING[sig]
    if sig == "n":
        return {
            # i32 pending, depth 1 and 2, and a bare param alias pending.
            "q32": f"(i32.xor {P['p32']} {e})",
            "q32q32": f"(i32.add {P['p32']} (i32.xor {P['p32b']} {e}))",
            "qal32": f"(i32.sub {P['alias32']} {e})",
        }
    out = {
        # i64 pending, depth 1 (the issue's shape).
        "q64": f"(i64.add {P['p64']} {as64(e, w)})",
        # i32 pending, depth 1.
        "q32": (f"(i64.extend_i32_u (i32.xor {P['p32']} {e}))" if w == 32 else
                f"(i64.xor (i64.extend_i32_u {P['p32']}) {e})"),
        # i64 under i32, depth 2.
        "q64q32": (f"(i64.add {P['p64']} (i64.extend_i32_u (i32.xor {P['p32']} {e})))"
                   if w == 32 else
                   f"(i64.add {P['p64']} (i64.xor (i64.extend_i32_u {P['p32']}) {e}))"),
        # i64 under i64, depth 2.
        "q64q64": f"(i64.add {P['p64']} (i64.xor {P['p64b']} {as64(e, w)}))",
    }
    if P["alias32"]:
        out["qal32"] = (f"(i64.extend_i32_u (i32.sub {P['alias32']} {e}))" if w == 32 else
                        f"(i64.sub (i64.extend_i32_u {P['alias32']}) {e})")
    if P["alias64"]:
        out["qal64"] = f"(i64.sub {P['alias64']} {as64(e, w)})"
    return out


def build_module():
    funcs = []  # (name, sig, body)
    pre = lambda k: "(drop (i32.const 1)) " * k  # noqa: E731
    ops = ([(32, o) for o in I32_BIN + I32_UN] + [(64, o) for o in I64_BIN + I64_UN])
    for sig in ("w", "d", "n"):
        for width, op in ops:
            for form in ("p", "t"):
                if (sig, width, form) not in OPERANDS:
                    continue
                e = op_expr(sig, width, op, form)
                for sname, body in shapes_for(sig, e, width).items():
                    # The round-robin cursor is the trigger: k dropped
                    # constants advance it by k (9 allocatable registers).
                    for k in range(9):
                        funcs.append((f"{sig}_i{width}_{op}_{form}_{sname}_k{k}", sig,
                                      f"{pre(k)}{body}"))
    # The issue's own module, verbatim.
    funcs.append(("issue_div_s", "w", "local.get 0 i64.extend_i32_s i64.const 1000 i64.add "
                  "local.get 0 local.get 1 i32.div_s i64.extend_i32_s i64.add"))
    funcs.append(("issue_rem_u", "w", "local.get 0 i64.extend_i32_s i64.const 1000 i64.add "
                  "local.get 0 local.get 1 i32.rem_u i64.extend_i32_u i64.add"))
    wat = "(module\n" + "\n".join(
        f' (func (export "{n}") (param {" ".join(SIGS[g][0])}) (result {SIGS[g][1]}) {b})'
        for n, g, b in funcs) + ")\n"
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


def make_uc(text):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STK, 0x10000)
    mu.mem_write(CODE, text)
    return mu


def run(mu, syms, base, name, sig, args):
    global emulations
    if sig in ("w", "n"):
        words = [args[0] & M32, args[1] & M32, 0xFEEDFACE, 0xFEEDFACE]
    else:  # two i64 in r0:r1, r2:r3 (lo, hi)
        x, y = args[0] & M64, args[1] & M64
        words = [x & M32, x >> 32, y & M32, y >> 32]
    mu.reg_write(ac.UC_ARM_REG_SP, STK + 0xC000)
    mu.reg_write(ac.UC_ARM_REG_R11, LIN)
    mu.reg_write(ac.UC_ARM_REG_R10, 0x10000)
    for r, wv in zip((ac.UC_ARM_REG_R0, ac.UC_ARM_REG_R1, ac.UC_ARM_REG_R2,
                      ac.UC_ARM_REG_R3), words):
        mu.reg_write(r, wv)
    for r in (ac.UC_ARM_REG_R4, ac.UC_ARM_REG_R5, ac.UC_ARM_REG_R6, ac.UC_ARM_REG_R7,
              ac.UC_ARM_REG_R8, ac.UC_ARM_REG_R12):
        mu.reg_write(r, 0xFEEDFACE)
    mu.reg_write(ac.UC_ARM_REG_LR, RET | 1)
    emulations += 1
    try:
        mu.emu_start((CODE + ((syms[name] - base) & ~1)) | 1, RET, count=INSNS)
    except UcError as ex:
        return f"fault:{ex}"
    if mu.reg_read(ac.UC_ARM_REG_PC) & ~1 != RET & ~1:
        return "budget"
    return (mu.reg_read(ac.UC_ARM_REG_R0) & M32) | ((mu.reg_read(ac.UC_ARM_REG_R1) & M32) << 32)


def leg(engine, module, funcs, obj, label):
    """Returns (compared, failures, declined). Every export in this population
    compiles on a correct build, so a DECLINED export (a loud skip at compile
    time) is a failure too: it is not wrong code, but it would hide its shape
    from the comparison. Pre-#1712, i32.rotl's `rs <> rn` side condition made
    the temp-on-operand instance a loud decline rather than wrong code."""
    syms, text, base = load(obj)
    mu = make_uc(text)
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = inst.exports(store)
    checks = wrong = 0
    bad_names, declined = set(), []
    for name, sig, _ in funcs:
        if name not in syms:
            declined.append(name)
            continue
        for v in VECS[sig]:
            try:
                want = exports[name](store, *v) & (M64 if SIGS[sig][1] == "i64" else M32)
            except wasmtime.Trap:
                want = "trap"
            got = run(mu, syms, base, name, sig, v)
            if SIGS[sig][1] == "i32" and isinstance(got, int):
                got &= M32
            if isinstance(got, str) and got.startswith("fault:") and want == "trap":
                got = "trap"  # UDF is synth's trap
            checks += 1
            if got != want:
                wrong += 1
                bad_names.add(name)
                if wrong <= 40:
                    w = want if isinstance(want, str) else hex(want)
                    g = got if isinstance(got, str) else hex(got)
                    print(f"BUG [{label}] {name}{v}: want={w} got={g}")
    shapes = sorted({n.rsplit("_k", 1)[0] for n in bad_names})
    dshapes = sorted({n.rsplit("_k", 1)[0] for n in declined})
    print(f"[{label}] {checks - wrong}/{checks} vectors match wasmtime; "
          f"{len(bad_names)} wrong exports; {len(declined)} declined exports")
    if shapes:
        print(f"[{label}]   wrong shapes ({len(shapes)}): {shapes}")
    if dshapes:
        print(f"[{label}]   declined shapes ({len(dshapes)}): {dshapes}")
    return checks, wrong, len(declined)


def main():
    funcs, wat = build_module()
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, wat)
    total = total_wrong = total_declined = floor_fail = 0
    with tempfile.TemporaryDirectory() as td:
        wat_path = Path(td) / "pending_below_temp_1721.wat"
        wat_path.write_text(wat)
        for target in TARGETS:
            for label, reloc in (("relocatable", True), ("self-contained", False)):
                obj = os.path.join(td, f"{target}_{label}.o")
                p_cmd = [SYNTH, "compile", str(wat_path), "-t", target, "--all-exports",
                         "--allow-skipped-exports", "-o", obj]
                if reloc:
                    p_cmd.append("--relocatable")
                env = dict(os.environ, SYNTH_PATH_DEBUG="1")
                p = subprocess.run(p_cmd, capture_output=True, text=True, env=env)
                if p.returncode != 0:
                    die(f"compile failed ({target}/{label}):\n{p.stderr[-1500:]}")
                c, w, d = leg(engine, module, funcs, obj, f"{target}:{label}")
                total_declined += d
                if c < MIN_COMPARED_PER_LEG:
                    print(f"FAIL floor [{target}:{label}]: {c} compared < {MIN_COMPARED_PER_LEG}")
                    floor_fail += 1
                # The self-contained leg must really exercise the OPTIMIZED
                # path for the "n" group, or it would only re-test the direct
                # selector the relocatable leg already covers.
                opt = (p.stdout + p.stderr).count("[path-debug] optimized")
                print(f"[{target}:{label}] functions lowered by the optimized path: {opt}")
                if not reloc and opt < MIN_OPTIMIZED_SELF_CONTAINED:
                    print(f"FAIL floor [{target}:{label}]: {opt} optimized-path functions "
                          f"< {MIN_OPTIMIZED_SELF_CONTAINED}")
                    floor_fail += 1
                total += c
                total_wrong += w
    print(f"\n#1721 CHECKS={total - total_wrong}/{total} (emulations={emulations}, "
          f"exports={len(funcs)}, declined={total_declined})")
    bad = total_wrong or total_declined or floor_fail
    print("#1721 pending-below-temp ORACLE: " + ("FAIL" if bad else "PASS"))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
