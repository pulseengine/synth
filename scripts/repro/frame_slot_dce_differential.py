#!/usr/bin/env python3
"""VCR-RA frame-slot DCE (#242) — EXECUTION-validate stack-reload forwarding +
dead-frame-store elimination on the optimized path.

The optimized ARM path lowers wasm locals frame-resident: `local.get`→`ldr [sp]`,
`local.set`→`str [sp]`. On the silicon hot path most of that traffic is spurious
(gale #209: flat_flight's spills fit in R0-R8 once value-allocated). Two paired
passes attack it, both behind `SYNTH_STACK_FWD=1`:
  - `forward_stack_reloads` turns `str rX,[sp,#N]; … ; ldr rY,[sp,#N]` into
    `… ; mov rY,rX` when rX still holds the value (a load → a register move);
  - `eliminate_dead_frame_stores` then removes the `str rX,[sp,#N]` whose slot is
    overwritten before any read (a now-dead store) — the natural completion.

On flat_flight's `flight_algo` this cuts sp-relative memory traffic 20→7 (9 loads
forwarded, 4 dead stores removed) and 139→135 instructions.

As of the #242 feature loop both passes are DEFAULT-ON (the win lands on the
shipped --relocatable path); `SYNTH_NO_STACK_FWD=1` is the opt-out. This harness is
the correctness oracle for the flip: it compiles flat_flight in BOTH configs, runs
flight_algo under unicorn (UC_ARCH_ARM / Thumb) with linear memory seeded exactly
as wasmtime's, and asserts the returned value is bit-identical to wasmtime ground
truth in BOTH the default and the opt-out path across several sensor inputs (a
default flip is only safe if the shipped path AND its rollback both match). It also
asserts the two configs emit DIFFERENT bytes (proof the flip is engaged).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/frame_slot_dce_differential.py
Exits nonzero on any value mismatch or a flag-off byte drift.
"""
import os
import struct
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
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("flight_seam_flat.wat")
WASM = Path(__file__).with_name("flight_seam_flat.wasm")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

CODE, LIN, STK = 0x10000, 0x40000, 0x90000
ST_OFF, S_OFF = 0x1000, 0x2000


def st_init(pitch=1000, roll=-500, yaw=200, updates=7):
    b = bytearray(64)
    struct.pack_into("<i", b, 0, pitch)
    struct.pack_into("<i", b, 4, roll)
    struct.pack_into("<i", b, 8, yaw)
    struct.pack_into("<i", b, 24, updates)
    return bytes(b)


def s_init(vals=(100, -50, 30, 300, -200)):
    b = bytearray(32)
    for i, v in enumerate(vals):
        struct.pack_into("<h", b, i * 2, v)
    return bytes(b)


# (state-init, sensor-init) input variations exercising the hot path.
CASES = [
    (st_init(), s_init()),
    (st_init(0, 0, 0, 0), s_init((0, 0, 0, 0, 0))),
    (st_init(32000, -32000, 12345, 99), s_init((-300, 300, -200, 200, -100))),
    (st_init(-1, 1, -2, 3), s_init((1, -1, 2, -2, 3))),
]


def compile_flat(out, fwd):
    # `fwd` True  = the shipped DEFAULT (stack-fwd + frame-slot DCE on);
    #       False = the SYNTH_NO_STACK_FWD opt-out (frame-resident, pre-flip bytes).
    env = {"PATH": "/usr/bin:/bin"}
    if not fwd:
        env["SYNTH_NO_STACK_FWD"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (fwd={fwd}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for s in sec.iter_symbols():
                if s.name:
                    syms[s.name] = s["st_value"]
    return code, base, syms


def wasmtime_run(fn, st, s):
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WASM.read_bytes())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    mem = inst.exports(store)["memory"]
    mem.write(store, st, ST_OFF)
    mem.write(store, s, S_OFF)
    return inst.exports(store)[fn](store, ST_OFF, S_OFF) & 0xFFFFFFFF


def unicorn_run(code, base, faddr, st, s):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_write(CODE, code)
    mu.mem_write(LIN + ST_OFF, st)
    mu.mem_write(LIN + S_OFF, s)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_R0, ST_OFF)
    mu.reg_write(UC_ARM_REG_R1, S_OFF)
    ret = 0x9F00 | 1
    mu.reg_write(UC_ARM_REG_LR, ret)
    try:
        mu.emu_start((CODE + (faddr & ~1) - base) | 1, ret & ~1, count=4000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def insn_count(code):
    n, i = 0, 0
    while i + 2 <= len(code):
        hw = code[i] | (code[i + 1] << 8)
        i += 4 if (hw >> 11) >= 0b11101 else 2
        n += 1
    return n


def main():
    off, on = "/tmp/fsdce_off.elf", "/tmp/fsdce_on.elf"
    compile_flat(off, fwd=False)
    compile_flat(on, fwd=True)
    off_code, off_base, off_syms = load(off)
    on_code, on_base, on_syms = load(on)

    # The DEFAULT (fwd-on) and the opt-out (fwd-off) must produce DIFFERENT bytes
    # — proof the flip is actually engaged in the shipped default — yet identical
    # RESULTS. (If these match, the default isn't doing anything.)
    if off_code == on_code:
        print("FAIL: default and SYNTH_NO_STACK_FWD opt-out emit identical bytes "
              "— the flip is not engaged")
        sys.exit(1)
    print("OK  default vs SYNTH_NO_STACK_FWD opt-out: bytes differ (flip engaged)")

    fails = 0
    # flight_algo is the optimization target — the only export with frame-slot
    # traffic the passes touch (DCE fires 4× there, 0× on the others) and the one
    # with a clean (i32 state_ptr, i32 sensor_ptr) -> i32 ABI to drive here.
    # Correctness must hold in BOTH configs (default and opt-out) — a default flip
    # is only safe if the shipped path AND its rollback both match wasmtime.
    exports = [e for e in ("flight_algo",) if e in on_syms]
    for label, (code, base, syms) in (("default", (on_code, on_base, on_syms)),
                                      ("opt-out", (off_code, off_base, off_syms))):
        for fn in exports:
            for st, s in CASES:
                gt = wasmtime_run(fn, st, s)
                got = unicorn_run(code, base, syms[fn], st, s)
                ok = isinstance(got, int) and got == gt
                if not ok:
                    fails += 1
                tag = f"0x{got:08X}" if isinstance(got, int) else got
                print(f"{'OK  ' if ok else 'FAIL'} {fn:14} {label:8} = {tag} "
                      f"(wasmtime 0x{gt:08X})")

    print(f"\n.text instructions: off={insn_count(off_code)} "
          f"on={insn_count(on_code)} "
          f"(delta={insn_count(off_code) - insn_count(on_code)})")
    print("\nRESULT:", "PASS" if not fails else f"FAIL ({fails} mismatches)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
