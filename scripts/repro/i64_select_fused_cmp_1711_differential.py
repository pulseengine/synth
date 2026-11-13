#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 4188
"""#1711 — ARM: a MULTI-MOVE `select` whose condition is a fused compare.

THE DEFECT, as measured on main e918c711 (capstone/objdump over the ELF, never
`synth disasm` text). `sel(a, b) = select(-1, 0x123456789abcdef0, a == b)`,
`--relocatable -t cortex-m4f`:

    cmp   r0, r1            ; the comparison (SetCond + `cmp D,#0` deleted)
    it eq ; moveq r7, r2    ; lo <- v1.lo   retargeted NE -> EQ   (right)
    it ne ; movne r8, r3    ; hi <- v1.hi   still NE              (WRONG)
    it eq ; moveq r7, r4    ; lo <- v2.lo   still EQ              (WRONG)
    it eq ; moveq r8, r5    ; hi <- v2.hi   still EQ              (WRONG)

`sel(1,1)` returned the FALSE operand and `sel(1,2)` mixed the halves.

ROOT CAUSE: the VCR-SEL-004 cmp->select fusion
(`synth_synthesis::liveness::fuse_cmp_select_with_stats`) deletes the select's
`cmp D,#0` and retargets the predicated moves onto the comparison's flags — but
it retargeted only `movne dst,v1` plus an optional `moveq dst,v2` with the SAME
destination: the i32 select's shape. The i64-pair select
(`rule_i64_select`: movne lo; movne hi; moveq lo; moveq hi) and the in-place
pair select (`rule_i64_select_inplace`, the VFP f64 select: movne lo; movne
hi) carry more moves, and every move past the first kept reading NE/EQ — now of
the COMPARISON's flags. The fusion runs in `finish_allocated_stream`, shared by
the direct selector (`--relocatable`), the self-contained path (whose optimized
lowering DECLINES an i64 select and falls back to direct, #1213) and the A32
(cortex-r5) backend, so all three were wrong.

THE CLASS this oracle executes, against wasmtime on the same module:

  * `i64c_<k>`  i64 select of two i64 CONSTANTS on every fused i32 compare
                kind (eq ne lt_s lt_u gt_s gt_u le_s le_u ge_s ge_u, eqz)
  * `i64p_<k>`  i64 select of a REGISTER-resident i64 param and a computed one
  * `f64_<k>`   f64 select (bits returned via i64.reinterpret_f64): the
                in-place VFP pair select on a double-precision FPU, the soft
                i64-pair select elsewhere
  * `f32_<k>`, `i32_<k>`  single-move selects — the shape that was always
                right; a fix must not disturb it
  * `q64_<k>`   an i64-COMPARE condition (I64SetCond is never fused) — contrast
  * `chain2`    an i64 select whose v1 is another i64 select (on main only
                the OUTER one fuses; its `le_s` was wrong). The outer kind is
                deliberately not `ne`: with `c == NE` the un-retargeted
                `movne`s are right by coincidence, which is why `i64c_ne` and
                `i64p_ne` are green even on the broken binary
  * `feed_add`  an i64 select feeding i64 arithmetic — NOT fused today (the
                boolean is not provably dead before the add), a contrast

LEGS: Thumb-2 on cortex-m4, cortex-m4f and cortex-m7dp, each BOTH
`--relocatable` (direct selector) and self-contained; A32 on cortex-r5
`--relocatable`. An export a target honest-skips (f64 on a single-precision
FPU) is counted as skipped, but every i64 shape must be present on every leg
and the f64 shapes on cortex-m7dp, or the leg fails — a skip cannot make the
class vanish.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/i64_select_fused_cmp_1711_differential.py
"""
import os
import struct
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn
    UC_ARM_REG_C1_C0_2 = UC_ARM_REG_FPEXC = None

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, LIN = 0x100000, 0x40000
RET_PAD = CODE + 0x38000
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000
M32, M64 = 0xFFFFFFFF, (1 << 64) - 1
CORE_ARGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
MEM_POISON, REG_POISON = 0xDEADBEEF, 0xFEEDFACE

I32_CMPS = ["eq", "ne", "lt_s", "lt_u", "gt_s", "gt_u", "le_s", "le_u", "ge_s", "ge_u"]
I64_CMPS = I32_CMPS


def cond32(k):
    return "(i32.eqz (local.get 0))" if k == "eqz" else f"(i32.{k} (local.get 0) (local.get 1))"


def cond64(k):
    return "(i64.eqz (local.get 0))" if k == "eqz" else f"(i64.{k} (local.get 0) (local.get 1))"


def build_wat():
    """The fixture, generated so the population IS this code. Returns (wat, exports)

    exports: list of (name, signature) where signature names the arg/ret ABI.
    """
    fns, exports = [], []
    for k in I32_CMPS + ["eqz"]:
        c = cond32(k)
        fns.append(
            f'(func (export "i64c_{k}") (param i32 i32) (result i64)\n'
            f"  (select (i64.const -1) (i64.const 0x123456789abcdef0) {c}))"
        )
        exports.append((f"i64c_{k}", "ii_l"))
        fns.append(
            f'(func (export "i64p_{k}") (param i32 i32 i64) (result i64)\n'
            f"  (select (local.get 2) (i64.xor (local.get 2) (i64.const 0xff00ff00ff00ff00)) {c}))"
        )
        exports.append((f"i64p_{k}", "iil_l"))
        fns.append(
            f'(func (export "f64_{k}") (param i32 i32) (result i64)\n'
            f"  (i64.reinterpret_f64 (select (f64.const 1.5) (f64.const -2.25e300) {c})))"
        )
        exports.append((f"f64_{k}", "ii_l"))
        fns.append(
            f'(func (export "f32_{k}") (param i32 i32) (result i32)\n'
            f"  (i32.reinterpret_f32 (select (f32.const 1.5) (f32.const -7.75) {c})))"
        )
        exports.append((f"f32_{k}", "ii_i"))
        fns.append(
            f'(func (export "i32_{k}") (param i32 i32) (result i32)\n'
            f"  (select (i32.const 0x5a5a1234) (i32.const 0x0f0f9876) {c}))"
        )
        exports.append((f"i32_{k}", "ii_i"))
    for k in I64_CMPS + ["eqz"]:
        fns.append(
            f'(func (export "q64_{k}") (param i64 i64) (result i64)\n'
            f"  (select (i64.const -1) (i64.const 0x123456789abcdef0) {cond64(k)}))"
        )
        exports.append((f"q64_{k}", "ll_l"))
    fns.append(
        '(func (export "chain2") (param i32 i32) (result i64)\n'
        "  (select\n"
        "    (select (i64.const 0x1111111122222222) (i64.const 0x3333333344444444)"
        " (i32.lt_s (local.get 0) (local.get 1)))\n"
        "    (i64.const 0x5555555566666666)\n"
        "    (i32.le_s (local.get 0) (local.get 1))))"
    )
    exports.append(("chain2", "ii_l"))
    fns.append(
        '(func (export "feed_add") (param i32 i32) (result i64)\n'
        "  (i64.add\n"
        "    (select (i64.const 0x00000000ffffffff) (i64.const 0x7fffffff00000001)"
        " (i32.gt_u (local.get 0) (local.get 1)))\n"
        "    (i64.const 1)))"
    )
    exports.append(("feed_add", "ii_l"))
    return "(module\n" + "\n".join(fns) + "\n)\n", exports


# Pairs that separate every compare kind: equal, lt/gt both signs, and the
# signed/unsigned boundary pairs where lt_s and lt_u disagree.
I32_PAIRS = [
    (1, 1), (1, 2), (2, 1), (0, 0), (-5, -5), (-1, 1), (1, -1),
    (0x7FFFFFFF, -0x80000000), (-0x80000000, 0x7FFFFFFF), (0, -1),
]
I64_PAIRS = [
    (1, 1), (1, 2), (2, 1), (0, 0), (-1, 1), (1, -1),
    (0x100000000, 1),  # lo equal-ish, hi differs
    (0x100000005, 0x200000005),  # lo EQUAL, hi decides
    (-0x8000000000000000, 0x7FFFFFFFFFFFFFFF), (0, -1),
]
X64 = 0x0123456789ABCDEF


def vectors(sig):
    if sig in ("ii_l", "ii_i"):
        return [(a, b) for a, b in I32_PAIRS]
    if sig == "iil_l":
        return [(a, b, X64) for a, b in I32_PAIRS] + [(a, b, -X64) for a, b in I32_PAIRS[:4]]
    if sig == "ll_l":
        return list(I64_PAIRS)
    raise ValueError(sig)


def regs_for(sig, args):
    """AAPCS: i32 -> one word, i64 -> an even-aligned register pair."""
    words = []
    kinds = sig.split("_")[0]
    for t, v in zip(kinds, args):
        if t == "l":
            if len(words) % 2:
                words.append(REG_POISON)
            v &= M64
            words += [v & M32, v >> 32]
        else:
            words.append(v & M32)
    assert len(words) <= 4, (sig, args)
    return words


def die(msg):
    print(f"#1711 ORACLE: FAIL — {msg}")
    sys.exit(1)


def compile_fixture(wat_path, out, target, relocatable):
    cmd = [SYNTH, "compile", wat_path, "--target", target, "--all-exports",
           "--allow-skipped-exports", "-o", out]
    if relocatable:
        cmd.append("--relocatable")
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        die(f"synth compile failed ({' '.join(cmd)}):\n{p.stdout}\n{p.stderr}")


def load(path):
    """(symbols, .text, base_vaddr). The fixture has no calls, so ANY relocation
    against .text is unexpected and fails loudly rather than running unpatched."""
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
        sec = e.get_section_by_name(".text")
        if sec is None:
            die(f"no .text in {path}")
        base = sec["sh_addr"]
        text = sec.data()
        for rel in e.iter_sections():
            if rel["sh_type"] in ("SHT_REL", "SHT_RELA") and rel.name in (".rel.text", ".rela.text"):
                if rel.num_relocations():
                    die(f"{path}: unexpected .text relocations in a call-free fixture")
    return syms, bytes(text), base


def run(syms, text, base, name, words, thumb):
    addr = (syms[name] - base) & ~1
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
    try:
        from unicorn.arm_const import UC_CPU_ARM_MAX
        mu.ctl_set_cpu_model(UC_CPU_ARM_MAX)
    except (ImportError, AttributeError):
        pass
    mu.mem_map(CODE, 0x40000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    if len(text) > RET_PAD - CODE:
        die(f".text ({len(text)} B) overlaps the return pad")
    mu.mem_write(CODE, text)
    mu.mem_write(STACK_BASE, struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    if UC_ARM_REG_C1_C0_2 is not None:
        mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    mu.reg_write(UC_ARM_REG_SP, SP0)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    for i in range(4):
        mu.reg_write(CORE_ARGS[i], words[i] if i < len(words) else REG_POISON)
    entry = CODE + addr
    mu.reg_write(UC_ARM_REG_LR, RET_PAD | (1 if thumb else 0))
    try:
        mu.emu_start(entry | (1 if thumb else 0), RET_PAD, count=20000)
    except UcError as ex:
        return None, str(ex)
    if mu.reg_read(UC_ARM_REG_PC) & ~1 != RET_PAD & ~1:
        return None, "did not reach the return pad"
    return (mu.reg_read(UC_ARM_REG_R0) & M32) | ((mu.reg_read(UC_ARM_REG_R1) & M32) << 32), ""


def leg(engine, module, exports, obj, label, thumb, must_have):
    syms, text, base = load(obj)
    checks = fails = skipped = 0
    for name, sig in exports:
        if name not in syms:
            if must_have(name):
                fails += 1
                print(f"BUG [{label}] {name}: MISSING from .symtab (must lower on this leg)")
            skipped += 1
            continue
        for args in vectors(sig):
            store = wasmtime.Store(engine)
            inst = wasmtime.Instance(store, module, [])
            want = inst.exports(store)[name](store, *args)
            got, err = run(syms, text, base, name, regs_for(sig, args), thumb)
            if sig.endswith("_i"):
                want &= M32
                got = None if got is None else got & M32
            else:
                want &= M64
            checks += 1
            if got != want:
                fails += 1
                shown = f"{got:#x}" if got is not None else f"ERR({err})"
                print(f"BUG [{label}] {name}{tuple(args)}: want={want:#x} got={shown}")
    print(f"[{label}] {checks - fails}/{checks} vectors match wasmtime "
          f"({skipped} export(s) skipped by the target)")
    return checks, fails


def main():
    wat, exports = build_wat()
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, wat)
    i64_shape = ("i64c_", "i64p_", "q64_", "chain2", "feed_add")

    def must(target):
        def f(name):
            if name.startswith(i64_shape):
                return True
            return target == "cortex-m7dp" and name.startswith(("f64_", "f32_"))
        return f

    legs = []
    for target in ("cortex-m4", "cortex-m4f", "cortex-m7dp"):
        legs.append((target, True, True))
        legs.append((target, False, True))
    legs.append(("cortex-r5", True, False))

    total_checks = total_fails = 0
    with tempfile.TemporaryDirectory() as td:
        wat_path = os.path.join(td, "sel1711.wat")
        with open(wat_path, "w") as fh:
            fh.write(wat)
        for target, reloc, thumb in legs:
            label = f"{target} {'relocatable' if reloc else 'self-contained'}"
            obj = os.path.join(td, f"sel1711_{target}_{int(reloc)}.o")
            compile_fixture(wat_path, obj, target, reloc)
            c, f = leg(engine, module, exports, obj, label, thumb, must(target))
            total_checks += c
            total_fails += f

    print(f"\n#1711 CHECKS={total_checks - total_fails}/{total_checks}")
    if total_checks == 0:
        die("executed nothing")
    print("#1711 fused-compare multi-move select ORACLE: " + ("FAIL" if total_fails else "PASS"))
    sys.exit(1 if total_fails else 0)


if __name__ == "__main__":
    main()
