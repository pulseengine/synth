#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 3
"""#936 soundness cross-check: `I64Const`/`I64Ldr`/`I64Str` are now PRICED
(bounded), not declined, in the WCET cycle model. Compile three LEAF
fixtures — `i64.const`, `i64.store`, `i64.load` — via `--relocatable` (#197:
the ONLY compile path that reaches these pseudo-ops as real `ArmOp`s;
`select_with_stack`, forced by `--relocatable`), execute each under unicorn
(Thumb-2), and confirm:

  1. the functional result matches the WASM-semantics ground truth (a wrong
     MOVW/MOVT half-split, or a dropped address-materialization ADD.W in
     `i64_effective_base`, would change it);
  2. bound_cycles >= executed machine instructions (every machine
     instruction costs >= 1 cycle) — the priced bound is a sound ceiling on
     the ACTUAL execution, not a guessed constant.

These fixtures are deliberately LEAF (no direct calls): a `--relocatable`
object's direct-call `BL`s carry UNRESOLVED relocations (the CLI itself says
"requires linking with Kiln bridge") — following one under unicorn without a
link step would execute the wrong target. The cascade/composition half of
#936 (a caller that was `callee-unbounded` resolving to bounded once its
i64.load leaf prices) is instead pinned analytically in the cargo gate
(`wcet_bound_gate.rs`, exact composed literal), matching how the existing
phase-3 composition script is scoped relative to its own cargo-gate pin.

This is the execution-side evidence the cargo gate cannot produce in-CI (no
unicorn dep there); the gate pins the same three fixtures' exact cycle
literals (52 / 72 / 54 at authoring, debug build, cortex-m4).

Usage:
    SYNTH=/path/to/synth python3 scripts/repro/wcet_phase6_936_i64_leaf_soundness.py
Requires: pip install unicorn pyelftools
"""
import json
import os
import subprocess
import sys

from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
from unicorn.arm_const import (
    UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_SP, UC_ARM_REG_LR,
    UC_ARM_REG_PC, UC_ARM_REG_R10, UC_ARM_REG_R11,
)

# Reuse the phase-2 harness's ELF/sidecar plumbing verbatim.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wcet_phase2_778_unicorn_soundness import load_elf, sidecar_entry  # noqa: E402

SYNTH = os.environ.get("SYNTH", "synth")
RETURN_MAGIC = 0x0000FFFE  # even address outside .text: stop when PC reaches it
MEM_BASE = 0x20000100  # matches the R10==R11 linear-memory-base convention
# `i64_effective_base` (arm_encoder.rs) and the phase-2/3/4/5 scripts' `run_func`
# both key off — see `generate_i64_store_with_bounds_check`'s doc: "R11 = memory
# base".


def compile_wat_relocatable(wat_path, elf_path):
    """Like phase2's `compile_wat`, but forces `--relocatable` (#197) — the
    ONLY path that lowers `i64.const`/`i64.load`/`i64.store` onto the
    `I64Const`/`I64Ldr`/`I64Str` `ArmOp`s this fix prices. Without it these
    fixtures would compile through the OPTIMIZED selector, which never emits
    those pseudo-ops at all (see `coverage()` in
    `estimator_encoder_agreement.rs`) — silently testing nothing."""
    cmd = [
        SYNTH, "compile", wat_path, "-o", elf_path,
        "-t", "cortex-m4", "--relocatable", "--emit-wcet",
    ]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    assert r.returncode == 0, r.stderr
    return json.load(open(elf_path + ".wcet.json"))


def run_leaf(text, text_addr, addr, args=(), mem_writes=()):
    """Like phase2's `run_func`, extended with an OPTIONAL linear-memory
    pre-seed (for the `i64.load` fixture) and returning both halves of an
    i64 result (`r0`=lo, `r1`=hi — AAPCS i64-in-register-pair) plus the raw
    `Uc` instance so a caller can inspect memory afterward (the `i64.store`
    fixture)."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    base = text_addr & ~0xFFF
    size = ((text_addr + len(text) - base) + 0xFFF) & ~0xFFF
    mu.mem_map(base, max(size, 0x1000))
    mu.mem_write(text_addr, text)
    mu.mem_map(0x20000000, 0x40000)  # linear memory + stack RAM
    mu.mem_map(RETURN_MAGIC & ~0xFFF, 0x1000)
    for waddr, wval in mem_writes:
        mu.mem_write(waddr, wval)
    mu.reg_write(UC_ARM_REG_SP, 0x2003FF00)
    mu.reg_write(UC_ARM_REG_LR, RETURN_MAGIC | 1)  # thumb return-to-magic
    mu.reg_write(UC_ARM_REG_R10, MEM_BASE)
    mu.reg_write(UC_ARM_REG_R11, MEM_BASE)
    for i, v in enumerate(args):
        mu.reg_write(UC_ARM_REG_R0 + i, v)

    counted = {"n": 0}

    def hook(mu_, addr_, size_, _):
        counted["n"] += 1
        if counted["n"] > 5_000_000:
            mu_.emu_stop()

    mu.hook_add(UC_HOOK_CODE, hook)
    mu.emu_start(addr | 1, RETURN_MAGIC, timeout=10_000_000)
    assert mu.reg_read(UC_ARM_REG_PC) & ~1 == RETURN_MAGIC, (
        f"did not return: pc={mu.reg_read(UC_ARM_REG_PC):#x} "
        f"after {counted['n']} insns"
    )
    return mu.reg_read(UC_ARM_REG_R0), mu.reg_read(UC_ARM_REG_R1), counted["n"], mu


# `i64.const 1000000`: lo32=0xF4240 (>0xFFFF, needs MOVT), hi32=0 (no MOVT) —
# 3 MOVW/MOVT instructions, mirrors gale's gust:os/time@0.1.0#resolution
# I64Const decline.
K_WAT = r"""
(module
  (func (export "k") (result i64)
    i64.const 1000000))
"""

# `i64.store` a constant to [mem_base + param]: no index-register address
# materialization needed at the STORE site itself (the address IS the param,
# no static memarg offset) — mirrors gale's exec_admit I64Str decline.
STR_WAT = r"""
(module
  (memory 1)
  (func (export "st") (param i32)
    local.get 0
    i64.const 42
    i64.store))
"""

# `i64.load` from [mem_base + param] — mirrors gale's
# gust:os/timer@0.1.0#slept-shaped I64Ldr decline (I64Ldr shares
# `i64_effective_base` with I64Str and is priced alongside it in #936 to
# avoid an identical cascade-blocking decline).
LDR_WAT = r"""
(module
  (memory 1)
  (func (export "ld") (param i32) (result i64)
    local.get 0
    i64.load))
"""


def main():
    d = os.environ.get("WCET_REPRO_DIR", "/tmp/wcet_phase6_936_repro")
    os.makedirs(d, exist_ok=True)
    os.chdir(d)

    print("== I64Const: i64.const 1000000 (needs a MOVT on the lo half only) ==")
    open("k.wat", "w").write(K_WAT)
    report = compile_wat_relocatable("k.wat", "k.o")
    f = sidecar_entry(report, "k")
    assert f["status"] == "bounded", f"k: expected bounded (I64Const priced), got {f}"
    text, text_addr, syms = load_elf("k.o")
    r0, r1, n, _ = run_leaf(text, text_addr, syms["k"])
    assert r0 == 1000000 and r1 == 0, f"k: r0:r1 = {r0:#x}:{r1:#x}, expected 1000000:0"
    bound = f["cycles"]
    assert bound >= n, f"k: UNSOUND — bound {bound} cycles < {n} executed insns"
    print(f"  OK k: r0:r1={r0}:{r1}, {n} insns <= bound {bound} cycles")

    print("== I64Str: i64.store 42 at [mem_base+param], no index materialization ==")
    open("st.wat", "w").write(STR_WAT)
    report = compile_wat_relocatable("st.wat", "st.o")
    f = sidecar_entry(report, "st")
    assert f["status"] == "bounded", f"st: expected bounded (I64Str priced), got {f}"
    text, text_addr, syms = load_elf("st.o")
    off = 16
    _, _, n, mu = run_leaf(text, text_addr, syms["st"], args=(off,))
    stored = mu.mem_read(MEM_BASE + off, 8)
    got = int.from_bytes(stored, "little")
    assert got == 42, f"st: stored value {got} != 42 — address materialization is wrong"
    bound = f["cycles"]
    assert bound >= n, f"st: UNSOUND — bound {bound} cycles < {n} executed insns"
    print(f"  OK st: mem[+{off}]={got}, {n} insns <= bound {bound} cycles")

    print("== I64Ldr: i64.load from [mem_base+param] ==")
    open("ld.wat", "w").write(LDR_WAT)
    report = compile_wat_relocatable("ld.wat", "ld.o")
    f = sidecar_entry(report, "ld")
    assert f["status"] == "bounded", f"ld: expected bounded (I64Ldr priced), got {f}"
    text, text_addr, syms = load_elf("ld.o")
    off = 24
    seed = 0x1122334455667788
    r0, r1, n, _ = run_leaf(
        text, text_addr, syms["ld"], args=(off,),
        mem_writes=[(MEM_BASE + off, seed.to_bytes(8, "little"))],
    )
    got = (r1 << 32) | r0
    assert got == seed, f"ld: r0:r1 = {r0:#x}:{r1:#x}, expected {seed:#x}"
    bound = f["cycles"]
    assert bound >= n, f"ld: UNSOUND — bound {bound} cycles < {n} executed insns"
    print(f"  OK ld: r0:r1={r0:#x}:{r1:#x}, {n} insns <= bound {bound} cycles")

    print("\nALL PHASE-6 (#936) I64CONST/I64STR/I64LDR LEAF SOUNDNESS CHECKS PASSED")


if __name__ == "__main__":
    sys.exit(main())
