#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 800
"""I64TEE (#1713, and the optimized-path half #1241) — every kind of i64
local round trip (`local.set` / `local.tee` / `local.get`, params and
non-params, straight-line, in blocks, ifs and loops), executed against
wasmtime on BOTH selectors.

WHAT WAS WRONG — one defect, two sites.

1. DIRECT selector (`select_with_stack`, #1713). The local-width set the
   selector consults was the dataflow walk `infer_i64_locals`, and the i64
   PARAMS were OR-ed into it only AFTER the walk. So `local.get 0` of an i64
   param pushed "32-bit" during the walk and `local.tee 1` / `local.set 1`
   inferred the copy target i32. `compute_local_promotion` then promoted it to
   ONE callee-saved register, and every copy dropped its high word
   (`f(-1)` = 0x00000000fffffffe, wasmtime 0xfffffffffffffffe) — while the
   frame layout, which OR-ed in the DECLARED widths (#1214), sized the same
   local 8 bytes. Two components disagreed about one local's width. The fix
   is one set (`function_i64_locals`): the signature's core-pair params and
   the declared-i64 non-param locals SEED the walk, and the walk runs to a
   fixpoint (a loop back-edge can read a local before its defining write in
   op order). Layout, promotion and the operand stack all consult it.

2. OPTIMIZED path (`optimizer_bridge`, #1241). It has no 64-bit non-param
   local model: `Store` moves ONE register (an i64 is two slot-stack entries,
   so `local.set` stored the HIGH half and left the low one on the stack) and
   an `I64Load` of a non-param local handed out a fresh, never-written pair.
   The backend pre-gate now routes every function touching a 64-bit
   non-param local (the SAME `function_i64_locals` set) to the direct
   selector — path-debug reason `i64-local` — and the bridge refuses an i64
   `local.set`/`local.tee` itself as a backstop.

3. The same round trip's i32 twin, found by this oracle's `loop_accum`: the
   direct selector's i32-param `local.set`/`local.tee` arms wrote
   `index_to_reg(idx)` (sequential numbering) while every `local.get` reads
   the AAPCS home — p1 of `(i64, i32)` lives in R2, the set wrote R1, so the
   write was lost (a decrement-to-zero loop never terminated). The arms now
   write the AAPCS home.

LEGS. `--relocatable` objects on cortex-m4 and cortex-m7dp (Thumb-2) and
cortex-r5 (A32), run under unicorn with the argument registers loaded per
AAPCS (an i64 in an even-aligned pair). The self-contained `--all-exports
--target cortex-m4` image — the OPTIMIZED path, the #1241 subject — and the
same with `--no-optimize`, each booted through its own shipped
`Reset_Handler` (the `self_contained_boot_sweep_1189` Image). Every leg
executes every shape below over every vector; R4-R11 and SP are checked
preserved on the relocatable legs. An RV32 `--relocatable` leg runs the
shapes free of i64 params (the walk is shared; see RV_LEGS for why the
i64-param shapes are excluded there) with s1-s10 and SP checked.

RED on main 332a22db (361 of 851 calls wrong): the param-copy shapes lose the
high word on every ARM leg; `set_shifted_i32` (an i32 param after an i64 one)
is written to the wrong register; #1241's three named shapes (`i64_local`,
`bl_brif_i64`, `f_brif`) are wrong on the optimized image; RV32 loud-skips
`loop_backedge_i32`. GREEN on the fix: 855 compared, 0 wrong.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/i64_local_roundtrip_1713_differential.py
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (UC_ARCH_ARM, UC_ARCH_RISCV, UC_MODE_ARM, UC_MODE_RISCV32,
                     UC_MODE_THUMB, Uc, UcError)
from unicorn import arm_const as A
from unicorn import riscv_const as RV

REPRO = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32, M64 = 0xFFFFFFFF, (1 << 64) - 1

# Each shape: (export, wat body incl. signature, list of argument tuples).
# i64 vectors carry a set high word, a clear high word, a carry across the
# word boundary and a sign-bit pattern, so a dropped or swapped half shows.
V64 = [-1, 0x1_0000_0000, 5, 0x1234_5678_9ABC_DEF0, -0x7FFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF]
SHAPES: list[tuple[str, str, list[tuple]]] = [
    # ---- param sources (the #1713 shape and its siblings) ----
    ("tee_param_add", "(param i64) (result i64) (local i64)"
     " local.get 0 local.tee 1 local.get 1 i64.add", [(v,) for v in V64]),
    ("tee_param_drop", "(param i64) (result i64) (local i64)"
     " local.get 0 local.tee 1 drop local.get 1 i64.const 1 i64.add", [(v,) for v in V64]),
    ("set_param", "(param i64) (result i64) (local i64)"
     " local.get 0 local.set 1 i64.const 3 local.get 1 i64.add", [(v,) for v in V64]),
    ("set_param_hi", "(param i32 i64) (result i64) (local i64)"
     " local.get 1 local.set 2 local.get 2 local.get 0 i64.extend_i32_u i64.add",
     [(7, v) for v in V64]),
    ("chain2", "(param i64) (result i64) (local i64 i64)"
     " local.get 0 local.set 1 local.get 1 local.tee 2 local.get 1 i64.xor local.get 2 i64.add",
     [(v,) for v in V64]),
    ("tee_tee", "(param i64) (result i64) (local i64 i64)"
     " local.get 0 local.tee 1 local.tee 2 local.get 1 i64.add local.get 2 i64.add",
     [(v,) for v in V64]),
    ("param_to_param", "(param i64 i64) (result i64)"
     " local.get 1 local.tee 0 local.get 0 i64.add", [(1, v) for v in V64]),
    ("param_pair_swap", "(param i64 i64) (result i64) (local i64)"
     " local.get 0 local.set 2 local.get 1 local.set 0 local.get 2 local.set 1"
     " local.get 0 local.get 1 i64.sub", [(v, 0x5_0000_0003) for v in V64]),
    ("param_shr", "(param i64) (result i64) (local i64)"
     " local.get 0 local.tee 1 i64.const 32 i64.shr_u local.get 1 i64.add", [(v,) for v in V64]),
    ("param_cmp", "(param i64) (result i32) (local i64)"
     " local.get 0 local.set 1 local.get 1 i64.const 0x100000000 i64.ge_u", [(v,) for v in V64]),
    # an i32 param whose AAPCS home a preceding i64 param SHIFTED (p1 of
    # `(i64, i32)` lives in R2): the set wrote R1 (sequential numbering)
    ("set_shifted_i32", "(param i64 i32) (result i64)"
     " local.get 1 i32.const 5 i32.add local.set 1 local.get 0 local.get 1 i64.extend_i32_u i64.add",
     [(v, c) for v in V64 for c in (0, 9)]),
    ("tee_shifted_i32", "(param i64 i32) (result i32)"
     " local.get 1 i32.const 3 i32.mul local.tee 1 local.get 1 i32.add", [(1, c) for c in (0, 7, -1)]),
    # ---- inside control flow ----
    ("block_tee", "(param i64) (result i64) (local i64)"
     " block local.get 0 local.tee 1 drop end local.get 1 local.get 1 i64.add", [(v,) for v in V64]),
    ("if_set", "(param i64 i32) (result i64) (local i64)"
     " local.get 1 if local.get 0 local.set 2 end local.get 2",
     [(v, c) for v in V64 for c in (0, 1)]),
    ("ifres_set", "(param i64 i32) (result i64) (local i64)"
     " local.get 1 if (result i64) local.get 0 else i64.const 0x700000007 end"
     " local.set 2 local.get 2 i64.const 1 i64.add", [(v, c) for v in V64 for c in (0, 1)]),
    ("blockres_set", "(param i64) (result i64) (local i64)"
     " block (result i64) local.get 0 end local.set 1 local.get 1", [(v,) for v in V64]),
    ("loop_tee", "(param i64) (result i64) (local i64 i32)"
     " loop local.get 0 local.tee 1 drop local.get 2 i32.const 1 i32.add local.tee 2"
     " i32.const 3 i32.lt_u br_if 0 end local.get 1", [(v,) for v in V64]),
    ("loop_backedge", "(param i64) (result i64) (local i64 i64 i32)"
     " loop local.get 1 local.set 2 local.get 0 local.set 1 local.get 3 i32.const 1"
     " i32.add local.tee 3 i32.const 2 i32.lt_u br_if 0 end local.get 2", [(v,) for v in V64]),
    ("loop_backedge_i32", "(param i32) (result i64) (local i64 i64 i32)"
     " loop local.get 1 local.set 2 local.get 0 i64.extend_i32_s local.set 1 local.get 3"
     " i32.const 1 i32.add local.tee 3 i32.const 2 i32.lt_u br_if 0 end local.get 2",
     [(x,) for x in (0, 5, -1, 0x7FFFFFFF)]),
    ("loop_accum", "(param i64 i32) (result i64) (local i64)"
     " block loop local.get 1 i32.eqz br_if 1 local.get 2 local.get 0 i64.add local.set 2"
     " local.get 1 i32.const 1 i32.sub local.set 1 br 0 end end local.get 2",
     [(v, n) for v in V64 for n in (0, 1, 3)]),
    # ---- non-param sources (#1241's three named shapes, and kin) ----
    ("i64_local", "(result i64) (local i64)"
     " i64.const 0x0123456789ABCDEF local.set 0 local.get 0 i64.const 1 i64.add", [()]),
    ("bl_brif_i64", "(param i32) (result i64) (local i64)"
     " block local.get 0 i32.const 0 i32.lt_s br_if 0 i64.const 0x1122334455667788"
     " local.set 1 end local.get 1", [(x,) for x in (0, 5, -1, 0x7FFFFFFF)]),
    ("f_brif", "(result i32) (local i64)"
     " i64.const 0x100000005 block i32.const 1 br_if 0 end local.set 0 local.get 0"
     " i64.const 32 i64.shr_u i32.wrap_i64", [()]),
    ("const_tee", "(result i64) (local i64 i64)"
     " i64.const 0xFFFFFFFF00000001 local.tee 0 local.set 1 local.get 0 local.get 1 i64.add", [()]),
    ("extend_set", "(param i32) (result i64) (local i64)"
     " local.get 0 i64.extend_i32_s local.set 1 local.get 1 local.get 1 i64.mul",
     [(x,) for x in (0, 5, -1, 0x7FFFFFFF, -0x80000000)]),
    ("rbw_zero", "(param i64) (result i64) (local i64 i64)"
     " local.get 1 local.set 2 local.get 0 local.get 2 i64.add", [(v,) for v in V64]),
    ("local_to_local", "(param i32) (result i64) (local i64 i64)"
     " local.get 0 i64.extend_i32_u i64.const 32 i64.shl local.set 1"
     " local.get 1 local.set 2 local.get 2 local.get 1 i64.or",
     [(x,) for x in (0, 1, -1, 0x12345)]),
]

WAT = "(module\n" + "\n".join(
    f'  (func (export "{n}") {body})' for n, body, _ in SHAPES) + "\n)\n"

THUMB_LEGS = {
    "reloc-cortex-m4": ["--relocatable", "--all-exports", "-t", "cortex-m4"],
    "reloc-cortex-m7dp": ["--relocatable", "--all-exports", "-t", "cortex-m7dp"],
}
A32_LEGS = {
    "reloc-cortex-r5": ["--relocatable", "--all-exports", "-t", "cortex-r5"],
}
# RV32 shares the width walk (`infer_i64_locals`, now a fixpoint), so the
# shapes with NO i64 param execute there (a loud skip is counted, never
# compared). The i64-PARAM shapes are excluded on RV32 for a reason that is
# NOT this lane's: the RV32 selector declines an i64 param only when it is
# READ, and homes the params SEQUENTIALLY otherwise — p1 of `(i64, i32)` is
# read from a1, not a2 (ILP32 passes the i64 in a0:a1). That is a separate,
# pre-existing RV32 defect (identical bytes on 332a22db), reported with this
# lane rather than pinned here.
RV_LEGS = {
    "reloc-rv32imac": ["-b", "riscv", "--target", "riscv32imac", "--relocatable",
                       "--all-exports", "--allow-skipped-exports"],
}
SELF_LEGS = {
    "self-cortex-m4": ["--all-exports", "--target", "cortex-m4"],
    "self-cortex-m4-noopt": ["--all-exports", "--target", "cortex-m4", "--no-optimize"],
}

TEXT, STK, RET = 0x10000, 0x300000, 0x400000
POISON = 0xFEEDFACE
ARG_REGS = [A.UC_ARM_REG_R0, A.UC_ARM_REG_R1, A.UC_ARM_REG_R2, A.UC_ARM_REG_R3]
CALLEE = [getattr(A, f"UC_ARM_REG_R{i}") for i in range(4, 12)]


def words_for(ptypes, args):
    w = []
    for t, v in zip(ptypes, args):
        if t == "i64":
            if len(w) % 2:
                w.append(0)
            v &= M64
            w += [v & M32, v >> 32]
        else:
            w.append(v & M32)
    return w


def load_boot_sweep():
    spec = importlib.util.spec_from_file_location(
        "boot_sweep_1189", REPRO / "self_contained_boot_sweep_1189_differential.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def compile_leg(wat_path, out, flags):
    r = subprocess.run([SYNTH, "compile", str(wat_path), *flags, "-o", str(out)],
                       capture_output=True, text=True)
    return r


def reloc_runner(obj: Path, thumb: bool):
    with obj.open("rb") as fh:
        e = ELFFile(fh)
        text = e.get_section_by_name(".text").data()
        rel = e.get_section_by_name(".rel.text")
        if rel is not None and rel.num_relocations():
            raise SystemExit(f"harness: {obj} carries relocations; the shapes are call-free")
        st = next(s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols()
                if s.name and s["st_info"]["type"] == "STT_FUNC"}
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
    mu.mem_map(TEXT, 0x10000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(TEXT, text)

    def call(name, words, nres):
        for i, r in enumerate(ARG_REGS):
            mu.reg_write(r, words[i] if i < len(words) else POISON)
        seeds = {}
        for k, r in enumerate(CALLEE):
            seeds[r] = 0xC0DE0000 | k
            mu.reg_write(r, seeds[r])
        mu.reg_write(A.UC_ARM_REG_SP, STK)
        mu.reg_write(A.UC_ARM_REG_LR, RET | (1 if thumb else 0))
        addr = TEXT + syms[name]
        try:
            mu.emu_start(addr | (1 if thumb else 0), RET, count=200_000)
        except UcError as ex:
            return ("fault", str(ex)), []
        if (mu.reg_read(A.UC_ARM_REG_PC) & ~1) != RET:
            return ("timeout",), []
        viol = [f"R{4 + k} clobbered" for k, r in enumerate(CALLEE)
                if (mu.reg_read(r) & M32) != seeds[r]]
        if (mu.reg_read(A.UC_ARM_REG_SP) & M32) != STK:
            viol.append("SP imbalance")
        return ("ok", [mu.reg_read(r) & M32 for r in ARG_REGS[:nres]]), viol

    return call


def rv_runner(obj: Path):
    with obj.open("rb") as fh:
        e = ELFFile(fh)
        text = e.get_section_by_name(".text").data()
        for sec in e.iter_sections():
            if sec["sh_type"] in ("SHT_REL", "SHT_RELA") and sec.num_relocations():
                raise SystemExit(f"harness: {obj} carries relocations; the shapes are call-free")
        st = next(s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        syms = {s.name: s["st_value"] for s in st.iter_symbols()
                if s.name and s["st_info"]["type"] == "STT_FUNC"}
    a_regs = [getattr(RV, f"UC_RISCV_REG_A{i}") for i in range(8)]
    s_regs = [getattr(RV, f"UC_RISCV_REG_S{i}") for i in range(1, 11)]

    def call(name, words, nres):
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        mu.mem_map(TEXT, 0x10000)
        mu.mem_map(STK - 0x10000, 0x20000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(TEXT, text)
        for i, r in enumerate(a_regs):
            mu.reg_write(r, words[i] if i < len(words) else POISON)
        seeds = {r: 0xC0DE0100 | k for k, r in enumerate(s_regs)}
        for r, v in seeds.items():
            mu.reg_write(r, v)
        mu.reg_write(RV.UC_RISCV_REG_SP, STK)
        mu.reg_write(RV.UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(TEXT + syms[name], RET, count=200_000)
        except UcError as ex:
            return ("fault", str(ex)), []
        if mu.reg_read(RV.UC_RISCV_REG_PC) != RET:
            return ("timeout",), []
        viol = [f"s{k + 1} clobbered" for k, r in enumerate(s_regs)
                if (mu.reg_read(r) & M32) != seeds[r]]
        if (mu.reg_read(RV.UC_RISCV_REG_SP) & M32) != STK:
            viol.append("SP imbalance")
        return ("ok", [mu.reg_read(r) & M32 for r in a_regs[:nres]]), viol

    call.syms = syms
    return call


def main() -> int:
    eng = wasmtime.Engine()
    module = wasmtime.Module(eng, WAT)
    sigs = {}
    for exp in module.exports:
        sigs[exp.name] = ([str(p) for p in exp.type.params], [str(r) for r in exp.type.results])
    exp_cache = {}
    for name, _, vecs in SHAPES:
        for args in vecs:
            store = wasmtime.Store(eng)
            inst = wasmtime.Instance(store, module, [])
            r = inst.exports(store)[name](store, *args)
            rt = sigs[name][1][0]
            exp_cache[(name, args)] = (r & M64) if rt == "i64" else (r & M32)

    tmp = Path(tempfile.mkdtemp(prefix="i64tee1713-"))
    wat_path = tmp / "shapes.wat"
    wat_path.write_text(WAT)
    boot = load_boot_sweep()

    total_bad = 0
    total_cmp = 0
    leg_summary = []

    def compare(leg, call, present=None):
        nonlocal total_bad, total_cmp
        bad = 0
        bad_fns = {}
        n = 0
        for name, _, vecs in SHAPES:
            if present is not None and name not in present:
                continue
            n += len(vecs)
            pt, rt = sigs[name]
            nres = 2 if rt[0] == "i64" else 1
            for args in vecs:
                outcome, viol = call(name, words_for(pt, args), nres)
                want = exp_cache[(name, args)]
                total_cmp += 1
                if outcome[0] != "ok":
                    got = outcome
                    ok = False
                else:
                    res = outcome[1]
                    got = (res[0] | (res[1] << 32)) if nres == 2 else res[0]
                    ok = got == want and not viol
                if not ok:
                    bad += 1
                    bad_fns[name] = bad_fns.get(name, 0) + 1
                    if bad_fns[name] <= 1:
                        g = f"{got:#x}" if isinstance(got, int) else got
                        print(f"  BAD {leg} {name}{args}: wasmtime={want:#x} synth={g}"
                              + (f" {viol}" if viol else ""))
        total_bad += bad
        leg_summary.append(f"{leg}: {n - bad}/{n} ok"
                           + (f" (wrong: {', '.join(f'{k}x{v}' for k, v in sorted(bad_fns.items()))})"
                              if bad_fns else ""))

    for leg, flags in {**THUMB_LEGS, **A32_LEGS}.items():
        obj = tmp / f"{leg}.o"
        r = compile_leg(wat_path, obj, flags)
        if r.returncode:
            print(f"FAIL {leg}: compile rc={r.returncode}: {r.stderr.strip()[-300:]}")
            total_bad += 1
            leg_summary.append(f"{leg}: COMPILE-FAIL")
            continue
        compare(leg, reloc_runner(obj, leg in THUMB_LEGS))

    for leg, flags in RV_LEGS.items():
        obj = tmp / f"{leg}.o"
        r = compile_leg(wat_path, obj, flags)
        if r.returncode:
            print(f"FAIL {leg}: compile rc={r.returncode}: {r.stderr.strip()[-300:]}")
            total_bad += 1
            leg_summary.append(f"{leg}: COMPILE-FAIL")
            continue
        call = rv_runner(obj)
        present = {n for n, _, _ in SHAPES
                   if n in call.syms and "i64" not in sigs[n][0]}
        leg_summary.append(f"{leg}: {len(present)} of {len(SHAPES)} shapes accepted "
                           f"and free of i64 params (the rest loud-skipped or excluded)")
        compare(leg, call, present)

    for leg, flags in SELF_LEGS.items():
        elf = tmp / f"{leg}.elf"
        r = compile_leg(wat_path, elf, flags)
        if r.returncode:
            print(f"FAIL {leg}: compile rc={r.returncode}: {r.stderr.strip()[-300:]}")
            total_bad += 1
            leg_summary.append(f"{leg}: COMPILE-FAIL")
            continue
        img = boot.Image(elf)
        if img.boot != "ok":
            print(f"FAIL {leg}: {img.boot}")
            total_bad += 1
            continue
        compare(leg, img.call)

    print("\n".join(leg_summary))
    print(f"SUMMARY: {total_cmp} calls compared, {total_bad} wrong")
    if total_cmp < 800:
        print("FAIL: vacuous run (fewer than 800 comparisons)")
        return 1
    if total_bad:
        print("FAIL: i64 local round trip diverges from wasmtime (#1713 / #1241)")
        return 1
    print("PASS: every i64 local round trip matches wasmtime on every leg")
    return 0


if __name__ == "__main__":
    sys.exit(main())
