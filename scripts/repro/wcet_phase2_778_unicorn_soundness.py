#!/usr/bin/env python3
"""#778 phase 2 soundness cross-check: execute compiled loop fixtures under
unicorn (Thumb-2), count machine instructions, and check:

  1. the functional result (r0) matches the WASM-semantics ground truth --
     a wrong derived trip count would change it;
  2. bound_cycles >= executed_instructions (every instruction costs >= 1
     cycle, so a bound below the executed-instruction count is UNSOUND);
  3. adversarial shapes (conditional counter store) stay DECLINED, and a
     deliberately-wrong --wcet-hints entry (below the real trip count) is
     REJECTED `hint-below-derived-trip` (red-first).

This is the execution-side evidence the cargo gate (wcet_bound_gate.rs)
cannot produce in-CI (no unicorn dependency there); the gate pins the same
fixtures analytically (exact literals + trip-aware floor). Observed at
authoring (v0.47 branch, debug build): sum10 r0=45 188<=349, bottom r0=45
129<=229, nested r0=15 377<=863, eqexit(hint 8) r0=28 126<=254, step3 r0=7
130<=254, memloop r0=11 304<=520, trip0 r0=0 18<=58; condstore declined;
eqexit hint 3 rejected hint-below-derived-trip.

Usage:
    SYNTH=/path/to/synth python3 scripts/repro/wcet_phase2_778_unicorn_soundness.py
Requires: pip install unicorn pyelftools
"""
import json
import os
import subprocess
import sys

from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
from unicorn.arm_const import (
    UC_ARM_REG_R0, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC,
    UC_ARM_REG_R10, UC_ARM_REG_R11,
)
from elftools.elf.elffile import ELFFile

SYNTH = os.environ.get("SYNTH", "synth")
RETURN_MAGIC = 0x0000FFFE  # even address outside .text: stop when PC reaches it


def compile_wat(wat_path, elf_path, hints=None):
    cmd = [SYNTH, "compile", wat_path, "-o", elf_path, "-t", "cortex-m4", "--emit-wcet"]
    if hints:
        cmd += ["--wcet-hints", hints]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    assert r.returncode == 0, r.stderr
    return json.load(open(elf_path + ".wcet.json"))


def load_elf(elf_path):
    """Return (text_bytes, text_addr, {name: func_addr})."""
    with open(elf_path, "rb") as f:
        elf = ELFFile(f)
        text = None
        for seg in elf.iter_sections():
            if seg.name == ".text":
                text = (seg.data(), seg["sh_addr"])
        syms = {}
        for sec in elf.iter_sections():
            if sec["sh_type"] == "SHT_SYMTAB":
                for s in sec.iter_symbols():
                    if s["st_info"]["type"] == "STT_FUNC":
                        syms[s.name] = s["st_value"]
        return text[0], text[1], syms


def run_func(text, text_addr, addr, args=()):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    base = text_addr & ~0xFFF
    size = ((text_addr + len(text) - base) + 0xFFF) & ~0xFFF
    mu.mem_map(base, max(size, 0x1000))
    mu.mem_write(text_addr, text)
    mu.mem_map(0x20000000, 0x40000)  # linear memory + stack RAM
    mu.mem_map(RETURN_MAGIC & ~0xFFF, 0x1000)
    mu.reg_write(UC_ARM_REG_SP, 0x2003FF00)
    mu.reg_write(UC_ARM_REG_LR, RETURN_MAGIC | 1)  # thumb return-to-magic
    mu.reg_write(UC_ARM_REG_R10, 0x20000100)
    mu.reg_write(UC_ARM_REG_R11, 0x20000100)
    for i, v in enumerate(args):
        mu.reg_write(UC_ARM_REG_R0 + i, v)

    counted = {"n": 0}

    def hook(mu_, addr_, size_, _):
        counted["n"] += 1
        if counted["n"] > 5_000_000:
            mu_.emu_stop()

    mu.hook_add(UC_HOOK_CODE, hook)
    mu.emu_start(addr | 1, RETURN_MAGIC, timeout=10_000_000)
    assert mu.reg_read(UC_ARM_REG_PC) & ~1 == RETURN_MAGIC, \
        f"did not return: pc={mu.reg_read(UC_ARM_REG_PC):#x} after {counted['n']} insns"
    return mu.reg_read(UC_ARM_REG_R0), counted["n"]


def sidecar_entry(report, name):
    for f in report["functions"]:
        if f["name"] == name:
            return f
    raise KeyError(name)


def check(name, report, elf_path, expect_r0, args=(), expect_status="bounded"):
    f = sidecar_entry(report, name)
    assert f["status"] == expect_status, f"{name}: {f}"
    text, text_addr, syms = load_elf(elf_path)
    r0, n_exec = run_func(text, text_addr, syms[name], args)
    # unicorn's hook counts each IT-block micro-op and each 16/32-bit insn once;
    # ArmOp-level instr counts differ (SetCond = 3 machine insns) — that's fine:
    # the check direction only needs executed MACHINE insns vs cycle bound.
    assert r0 == expect_r0 & 0xFFFFFFFF, f"{name}: r0={r0} expected {expect_r0}"
    if expect_status == "bounded":
        cyc = f["cycles"]
        assert cyc >= n_exec, \
            f"{name}: UNSOUND — bound {cyc} cycles < {n_exec} executed instructions"
        print(f"  OK {name}: r0={r0}, executed {n_exec} machine insns <= bound {cyc} cycles"
              f" (loops: {[(l['trip_count'], l['source']) for l in f.get('loops', [])]})")
    else:
        print(f"  OK {name}: r0={r0}, executed {n_exec}, status={f['status']} (decline honest)")


WAT = r"""
(module
  (func (export "sum10") (result i32)
    (local i32 i32)
    (block (loop
      local.get 0 i32.const 10 i32.lt_s i32.eqz br_if 1
      local.get 1 local.get 0 i32.add local.set 1
      local.get 0 i32.const 1 i32.add local.set 0
      br 0))
    local.get 1)
  (func (export "bottom") (result i32)
    (local i32 i32)
    (loop
      local.get 1 local.get 0 i32.add local.set 1
      local.get 0 i32.const 1 i32.add local.tee 0
      i32.const 10 i32.lt_s br_if 0)
    local.get 1)
  (func (export "nested") (result i32)
    (local i32 i32 i32)
    (block (loop
      local.get 0 i32.const 5 i32.lt_s i32.eqz br_if 1
      i32.const 0 local.set 1
      (block (loop
        local.get 1 i32.const 3 i32.lt_s i32.eqz br_if 1
        local.get 2 i32.const 1 i32.add local.set 2
        local.get 1 i32.const 1 i32.add local.set 1
        br 0))
      local.get 0 i32.const 1 i32.add local.set 0
      br 0))
    local.get 2)
  (func (export "eqexit") (result i32)
    (local i32 i32)
    (block (loop
      local.get 0 i32.const 8 i32.eq br_if 1
      local.get 1 local.get 0 i32.add local.set 1
      local.get 0 i32.const 1 i32.add local.set 0
      br 0))
    local.get 1)
  (func (export "step3") (result i32)
    (local i32 i32)
    (block (loop
      local.get 0 i32.const 20 i32.lt_s i32.eqz br_if 1
      local.get 1 i32.const 1 i32.add local.set 1
      local.get 0 i32.const 3 i32.add local.set 0
      br 0))
    local.get 1)
  (func (export "memloop") (result i32)
    (local i32)
    (block (loop
      local.get 0 i32.const 16 i32.lt_s i32.eqz br_if 1
      local.get 0 i32.const 4 i32.mul
      local.get 0
      i32.store
      local.get 0 i32.const 1 i32.add local.set 0
      br 0))
    i32.const 44 i32.load)
  (func (export "trip0") (result i32)
    (local i32 i32)
    (block (loop
      local.get 0 i32.const 0 i32.lt_s i32.eqz br_if 1
      local.get 1 i32.const 1 i32.add local.set 1
      local.get 0 i32.const 1 i32.add local.set 0
      br 0))
    local.get 1)
  (memory 1))
"""

ADVERSARIAL_WAT = r"""
(module
  ;; conditional extra store to the counter inside the body (two stores) —
  ;; the analyzer must NOT prove this shape
  (func (export "condstore") (param i32) (result i32)
    (local i32 i32)
    (block (loop
      local.get 1 i32.const 10 i32.lt_s i32.eqz br_if 1
      (if (local.get 0) (then local.get 1 i32.const 5 i32.add local.set 1))
      local.get 1 i32.const 1 i32.add local.set 1
      br 0))
    local.get 1)
  ;; infinite loop shape (no exit) — must decline
  ;; (kept commented: wasmtime/unicorn can't run it; the analyzer path is
  ;;  covered by databound in the main gate)
  (memory 1))
"""


def main():
    d = os.environ.get("WCET_REPRO_DIR", "/tmp/wcet_phase2_778_repro")
    os.makedirs(d, exist_ok=True)
    os.chdir(d)
    open("val.wat", "w").write(WAT)
    open("adv.wat", "w").write(ADVERSARIAL_WAT)
    open("val_hints.json", "w").write(json.dumps({
        "schema": "synth-wcet-hints-v1",
        "functions": {"eqexit": {"loop_bounds": [8]}},
    }))

    print("== main fixtures (with correct eqexit hint) ==")
    report = compile_wat("val.wat", "val.elf", hints="val_hints.json")
    check("sum10", report, "val.elf", 45)
    check("bottom", report, "val.elf", 45)
    check("nested", report, "val.elf", 15)
    check("eqexit", report, "val.elf", 28)
    check("step3", report, "val.elf", 7)      # v: 0,3,..,18 -> 7 trips
    check("memloop", report, "val.elf", 11)   # mem[44] = 11 (11*4=44)
    check("trip0", report, "val.elf", 0)      # 0 iterations, head runs once

    print("== adversarial: must stay declined ==")
    report = compile_wat("adv.wat", "adv.elf")
    f = sidecar_entry(report, "condstore")
    assert f["status"] == "declined" and f["reason"] == "loop", f
    # execute it anyway to show the decline was honest, not vacuous
    text, ta, syms = load_elf("adv.elf")
    r0, n = run_func(text, ta, syms["condstore"], (1,))
    print(f"  OK condstore: declined (two counter stores); runs fine r0={r0}")

    print("== red-first: wrong hint rejected ==")
    open("val_hints_wrong.json", "w").write(json.dumps({
        "schema": "synth-wcet-hints-v1",
        "functions": {"eqexit": {"loop_bounds": [3]}},
    }))
    report = compile_wat("val.wat", "val_wrong.elf", hints="val_hints_wrong.json")
    f = sidecar_entry(report, "eqexit")
    assert f["status"] == "declined", f
    assert f["hint_rejections"][0]["reason"] == "hint-below-derived-trip", f
    print("  OK eqexit with hint 3 (< real 8): REJECTED hint-below-derived-trip")

    print("ALL SOUNDNESS CHECKS PASSED")


if __name__ == "__main__":
    sys.exit(main())
