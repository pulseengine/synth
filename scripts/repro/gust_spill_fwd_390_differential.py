#!/usr/bin/env python3
"""#390 (VCR-RA) — EXECUTION-validate conditional-branch-transparent stack-reload
forwarding on the gust hot path, and own the SYNTH_NO_STACK_FWD flip-engagement
check.

The #390 size-attribution report measured `spill_reload` as gust_poll's biggest
overhead bucket (228 B / ~31%). The direct selector lowers gust_poll's `br_if`
ladders as compare→branch chains, and the pre-#390 `forward_stack_reloads`
stopped its forward scan at EVERY branch — so a value provably register-resident
across a conditional branch (fall-through edge, no register effect) was reloaded
from its frame slot anyway. The strengthened pass walks a holder lattice through
CONDITIONAL branches (joins — labels / resolved-branch targets — still reset all
state) and forwards or deletes those reloads: gust_poll 740 -> 722 B measured.

This harness is the execution oracle for that change:

  1. ENGAGEMENT — the shipped DEFAULT and the `SYNTH_NO_STACK_FWD=1` opt-out
     must emit DIFFERENT bytes on gust_kernel (the fixture where the lever is
     load-bearing; on flat_flight the downstream SYNTH_SPILL_REALLOC stages now
     reach the same bytes, so engagement is asserted HERE — see
     frame_slot_dce_differential.py's note).
  2. CORRECTNESS — gust_poll (state-mutating scheduler poll: return value AND
     the post-call state struct bytes) and gust_mix match wasmtime ground truth
     in ALL THREE configs: default, `SYNTH_NO_STACK_FWD=1`, and
     `SYNTH_SPILL_REALLOC=0` (a default is only safe if the shipped path and
     its rollbacks all match).

unicorn runs the DEFAULT-path standalone image exactly as Reset_Handler leaves
the machine: r9 = globals base (globals seeded 0x100000 / __data_end /
__heap_base), r10 = linmem size, r11 = linmem base, initial SP above linmem,
`.linear_memory` section contents loaded at the base.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/gust_spill_fwd_390_differential.py
Exits nonzero on identical engagement bytes or any execution mismatch.
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

REPO = Path(__file__).resolve().parents[2]
WASM = REPO / "scripts" / "repro" / "gust_kernel.wasm"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Reset_Handler's machine state (see the emitted prologue): linmem at
# 0x20000000, 17 pages = 0x110000 bytes, globals base right above it, initial
# SP at 0x20120000. Globals: [r9] = shadow-stack top, [r9,4] = __data_end,
# [r9,8] = __heap_base.
LIN = 0x2000_0000
LIN_SIZE = 0x11_0000
GLOBALS = 0x2011_0000
SP_INIT = 0x2012_0000
CODE = 0x0

STATE_OFF = 0x400  # word-aligned scratch offset in linear memory for the state
STATE_SPAN = 0x200  # bytes of state region compared after each call


def compile_cfg(out, env_extra):
    env = dict(os.environ)
    env.pop("SYNTH_NO_STACK_FWD", None)
    env.pop("SYNTH_SPILL_REALLOC", None)
    env.update(env_extra)
    r = subprocess.run(
        [SYNTH, "compile", str(WASM), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed ({env_extra}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    lin = f.get_section_by_name(".linear_memory")
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for s in sec.iter_symbols():
                if s.name:
                    syms[s.name] = s["st_value"]
    return text.data(), lin.data() if lin else b"", syms


def state_bytes(seed):
    # Deterministic pseudo-random state struct (xorshift), identical for
    # wasmtime and unicorn; both engines interpret the same bytes, so any
    # semantic divergence is a synth miscompile, not an input judgement.
    # The cursor/budget words at +0x30/+0x34 are clamped small: +0x34 seeds
    # the poll round's countdown (a random u32 there spins wasmtime for
    # minutes), +0x30 is the 0..5 slot cursor.
    x = seed or 0x9E3779B9
    out = bytearray()
    while len(out) < STATE_SPAN:
        x ^= (x << 13) & 0xFFFFFFFF
        x ^= x >> 17
        x ^= (x << 5) & 0xFFFFFFFF
        out += x.to_bytes(4, "little")
    out[0x30:0x34] = (seed % 6).to_bytes(4, "little")
    out[0x34:0x38] = (2 + seed % 5).to_bytes(4, "little")
    return bytes(out)


# (state, x, strict). strict=False marks the two zero-state cases KNOWN-
# DIVERGENT (#740): the direct path mistargets the loop-head empty-budget
# `br_if` to a mid-shape point after the first transition call, so synth
# spuriously writes state+0x34 (wasmtime writes nothing). Pre-existing on
# main v0.41.0, byte-identically in ALL lever configs — NOT a #390 regression.
# The xfail is anti-vacuous both ways: the RETURN value must still match, and
# the moment the memory divergence disappears (i.e. #740 is fixed) the case
# hard-fails and demands promotion to strict.
CASES = [
    (b"\x00" * STATE_SPAN, 0, False),
    (b"\x00" * STATE_SPAN, 7, False),
    (state_bytes(1), 3, True),
    (state_bytes(2), 0x1234, True),
    (state_bytes(3), -5 & 0xFFFFFFFF, True),
]


def wasmtime_poll(state, x):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WASM.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    mem = inst.exports(st)["memory"]
    mem.write(st, state, STATE_OFF)
    r = inst.exports(st)["gust_poll"](st, STATE_OFF, x - (1 << 32) if x >= 1 << 31 else x)
    return r & 0xFFFFFFFF, bytes(mem.read(st, STATE_OFF, STATE_OFF + STATE_SPAN))


def wasmtime_mix(x):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WASM.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    return inst.exports(st)["gust_mix"](st, x - (1 << 32) if x >= 1 << 31 else x) & 0xFFFFFFFF


def unicorn_call(text, lin_init, faddr, r0, r1):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    # Whole linmem + shadow stack + globals + machine stack, contiguous
    # (0x20000000..0x20120000) — exactly the Reset_Handler RAM layout.
    mu.mem_map(LIN, 0x12_0000)
    mu.mem_write(CODE, text)
    if lin_init:
        # .linear_memory carries the full initial linmem image.
        mu.mem_write(LIN, lin_init[:0x12_0000])
    # Reset_Handler machine state.
    mu.reg_write(UC_ARM_REG_R9, GLOBALS)
    mu.reg_write(UC_ARM_REG_R10, LIN_SIZE)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.mem_write(GLOBALS, (0x10_0000).to_bytes(4, "little"))
    mu.mem_write(GLOBALS + 4, (0x10_008F).to_bytes(4, "little"))
    mu.mem_write(GLOBALS + 8, (0x10_0090).to_bytes(4, "little"))
    mu.reg_write(UC_ARM_REG_SP, SP_INIT)
    ret = CODE + 0xFF00
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.reg_write(UC_ARM_REG_R0, r0)
    mu.reg_write(UC_ARM_REG_R1, r1)
    try:
        mu.emu_start((faddr & ~1) | 1, ret, timeout=5_000_000, count=200_000)
    except UcError as e:
        return f"ERR:{e}", None
    return (
        mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF,
        bytes(mu.mem_read(LIN + STATE_OFF, STATE_SPAN)),
    )


def main():
    cfgs = [
        ("default", {}),
        ("no-stack-fwd", {"SYNTH_NO_STACK_FWD": "1"}),
        ("no-spill-realloc", {"SYNTH_SPILL_REALLOC": "0"}),
    ]
    elves = {}
    for label, env in cfgs:
        out = f"/tmp/gust390_{label}.elf"
        compile_cfg(out, env)
        elves[label] = load(out)

    # 1. ENGAGEMENT: the SYNTH_NO_STACK_FWD lever must change gust_kernel's
    # bytes (this fixture is where the #390 conditional-branch-transparent
    # forwarding lives; an inert lever cannot pass).
    if elves["default"][0] == elves["no-stack-fwd"][0]:
        print("FAIL: default and SYNTH_NO_STACK_FWD opt-out emit identical bytes "
              "on gust_kernel — the stack-fwd lever is not engaged")
        sys.exit(1)
    print("OK  default vs SYNTH_NO_STACK_FWD opt-out: gust bytes differ (lever engaged)")

    fails = 0
    for label, _ in cfgs:
        text, lin_init, syms = elves[label]
        for state, x, strict in CASES:
            gt_ret, gt_mem = wasmtime_poll(state, x)
            # Seed the unicorn state region on a COPY of the initial image.
            lin = bytearray(lin_init) if lin_init else bytearray(LIN_SIZE)
            lin[STATE_OFF:STATE_OFF + STATE_SPAN] = state
            got_ret, got_mem = unicorn_call(text, bytes(lin), syms["gust_poll"], STATE_OFF, x)
            if strict:
                ok = got_ret == gt_ret and got_mem == gt_mem
                verdict = "OK  " if ok else "FAIL"
            elif got_ret == gt_ret and got_mem != gt_mem:
                ok = True  # the documented #740 divergence, return still exact
                verdict = "XF40"
            elif got_ret == gt_ret and got_mem == gt_mem:
                ok = False  # divergence gone: #740 fixed — promote to strict!
                verdict = "FIXD"
            else:
                ok = False
                verdict = "FAIL"
            fails += 0 if ok else 1
            tag = f"0x{got_ret:08X}" if isinstance(got_ret, int) else got_ret
            memtag = "mem==" if got_mem == gt_mem else "mem!="
            print(f"{verdict} gust_poll {label:16} x={x:>10} = {tag} "
                  f"(wasmtime 0x{gt_ret:08X}) {memtag}"
                  + ("" if strict else "  [known-divergent #740; FIXD ⇒ make strict]"))
        for x in (0, 1, 0x7FFF, 0x12345678, 0xFFFF_FF00):
            gt = wasmtime_mix(x)
            got, _ = unicorn_call(text, lin_init, syms["gust_mix"], x, 0)
            ok = got == gt
            fails += 0 if ok else 1
            tag = f"0x{got:08X}" if isinstance(got, int) else got
            print(f"{'OK  ' if ok else 'FAIL'} gust_mix  {label:16} x={x:>10} = {tag} "
                  f"(wasmtime 0x{gt:08X})")

    print("\nRESULT:", "PASS" if not fails else f"FAIL ({fails} mismatches)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
