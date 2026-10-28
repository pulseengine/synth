#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 42
"""#1580 — under --native-pointer-abi WITH a stack-pointer global, a constant
address plus a non-zero memarg offset is relocated on its EFFECTIVE address —
execution differential vs wasmtime.

THE DEFECT. With a stack-pointer global the selector relocated a constant
address by ONE of its two parts: the `i32.const` handler emits a constant
`C >= sp_init` as `__synth_wasm_data + C` (rule 1), and the #359/#739 dynamic
path emits a memarg `offset >= sp_init` as `__synth_wasm_data + offset`
(rule 2). The mixed split retargets each reloc to the `__synth_wasm_seg_K`
that holds its ADDEND, so when `C + offset` leaves that part's region the
access read the wrong region (`i32.const 0x1900 i32.load offset=0x704`, data
at 0x2000: synth 0x0, wasmtime 0x38373635), and when both parts qualified both
were relocated and the access faulted (`i32.const 0x900 i32.load
offset=0x1704`). `C = 0` was always correct: the addend was already the
effective address.

THE FIX (`InstructionSelector::npa_effective_addr_rewrite`). The offset is
folded into the constant that feeds the access (`i32.const C+O` with
`offset=0`, exact wasm — the producer is found by an exact backward stack walk
and is consumed only by the access), so the relocation carries `C + O` and the
existing retarget chooses the region that holds it. A constant routed through
a LOCAL cannot be folded (other reads share the definition), so a non-zero
offset on a rule-1 constant reached through a local is REFUSED loudly.

ROWS. Module `sp` (SP global 0x800, data at 0x900 / 0x2000 / 0x3000), one
instance per module, calls in order so a store is observed by the reads
after it. Every store row is read back through `i32.const 0 ... offset=EFF`
(the `C = 0` path, correct before and after) — never through the same shape
it was written with, which would agree with itself while both are wrong.
  x, y           — the issue's two rows (rule 1 + rule 2; rule 1 alone)
  r2             — rule 2 alone, `C = 4`: the offset is relocated, `+4` leaves
                   the gap into data at 0x2000
  same           — rule 1, `C + O` inside C's region (no-regression)
  gap / gap_st   — `C + O` in no segment (the zero reservation)
  ld8/ld16s/...  — narrow loads; i32 store/store8/store16; a store whose
                   value is computed (`i32.add`), which the positional guard
                   cannot see but the stack walk does
  i64*           — i64 load / load8_u / load32_s / store / store32
Module `fp` (cortex-m7dp): f32/f64 load and store, read as integers.

  loc_same*      — a rule-1 constant through a local plus an offset that stays
                   in the constant's own region (the #757 `[src + 0x20]`
                   shape): relocated exactly, must stay ACCEPTED and equal.

REFUSALS (must exit non-zero, name #1580, write no object), all through a
local, where the offset cannot be folded into the shared definition: a
relocated constant whose offset moves the access into a different data region
(`local.set`/`local.get` and `local.tee`, i32 and i64 loads); a scalar
constant whose relocated offset is retargeted into the wrong region (rule 2);
and a relocated constant plus a relocated offset inside one region (both parts
relocated — the address is doubled).

Harness: the hand linker of npa_const_addr_differential.py (.text/.data/.bss
at separate bases, R11 = 0), with R0-R10 and R12 seeded with garbage and the
stack below SP filled with a pattern before every call.

RED on the pre-fix binary (7e170d62): exits 1 — see RQ-89-NPAOFFSET.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/npa_offset_cross_segment_1580_differential.py
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from unicorn.arm_const import (
    UC_ARM_REG_C1_C0_2,
    UC_ARM_REG_FPEXC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R4,
    UC_ARM_REG_R5,
    UC_ARM_REG_R6,
    UC_ARM_REG_R7,
    UC_ARM_REG_R8,
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R12,
)

sys.path.insert(0, str(Path(__file__).parent))
import npa_const_addr_differential as h  # noqa: E402  (the shared hand linker)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
h.SYNTH = SYNTH

HDR = r"""(module (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x800))
  (data (i32.const 0x900) "\aa\bb\cc\dd")
  (data (i32.const 0x2000) "\31\32\33\34\35\36\37\38")
  (data (i32.const 0x3000) "\41\42\43\44\45\46\47\48")
"""

SP = HDR + r"""
  (func (export "anchor") (result i32) (i32.load (i32.const 0x900)))
  (func (export "x") (result i32) i32.const 0x900 i32.load offset=0x1704)
  (func (export "y") (result i32) i32.const 0x1900 i32.load offset=0x704)
  (func (export "r2") (result i32) i32.const 4 i32.load offset=0x1ffc)
  (func (export "same") (result i32) i32.const 0x2000 i32.load offset=4)
  (func (export "gap") (result i32) i32.const 0x900 i32.load offset=0x800)
  (func (export "ld8") (result i32) i32.const 0x1900 i32.load8_u offset=0x707)
  (func (export "ld16s") (result i32) i32.const 0x2800 i32.load16_s offset=0x806)
  (func (export "ld8x") (result i32) i32.const 0x900 i32.load8_u offset=0x2701)
  (func (export "rd2000") (result i32) i32.const 0 i32.load offset=0x2000)
  (func (export "rd2004") (result i32) i32.const 0 i32.load offset=0x2004)
  (func (export "rd3000") (result i32) i32.const 0 i32.load offset=0x3000)
  (func (export "rd3004") (result i32) i32.const 0 i32.load offset=0x3004)
  (func (export "rd1100") (result i32) i32.const 0 i32.load offset=0x1100)
  (func (export "st") i32.const 0x1900 i32.const 0x5a5b5c5d i32.store offset=0x704)
  (func (export "st8") i32.const 0x900 i32.const 0x99 i32.store8 offset=0x1701)
  (func (export "st16") i32.const 0x2800 i32.const 0x7766 i32.store16 offset=0x802)
  (func (export "stx") i32.const 0x1900 i32.const 3 i32.const 4 i32.add i32.store offset=0x1700)
  (func (export "gap_st") i32.const 0x900 i32.const 0x13579bdf i32.store offset=0x800)
  (func (export "i64ld") (result i64) i32.const 0x1900 i64.load offset=0x700)
  (func (export "i64ld8") (result i64) i32.const 0x900 i64.load8_u offset=0x2702)
  (func (export "i64ld32s") (result i64) i32.const 0x1900 i64.load32_s offset=0x1704)
  (func (export "i64st") i32.const 0x1900 i64.const 0x0102030405060708 i64.store offset=0x1700)
  (func (export "i64st32") i32.const 0x900 i64.const 0xfedcba98 i64.store32 offset=0x1704)
  (func (export "loc_same") (result i32) (local i32) i32.const 0x3000 local.set 0
    local.get 0 i32.load offset=4)
  (func (export "loc_same8") (result i32) (local i32) i32.const 0x2000 local.set 0
    local.get 0 i32.load8_u offset=6))"""

SP_SEQ = ["anchor", "x", "y", "r2", "same", "gap", "ld8", "ld16s", "ld8x",
          "st", "rd2004", "st8", "rd2000", "st16", "rd3000", "stx", "rd3000",
          "gap_st", "rd1100", "gap", "i64ld", "i64ld8", "i64ld32s",
          "i64st", "rd3000", "rd3004", "i64st32", "rd2004", "y", "x",
          "loc_same", "loc_same8"]

FP = HDR + r"""
  (func (export "anchor") (result i32) (i32.load (i32.const 0x900)))
  (func (export "f32ld") (result i32) i32.const 0x1900 f32.load offset=0x704 i32.reinterpret_f32)
  (func (export "f64ld") i32.const 0x3000 i32.const 0x900 f64.load offset=0x1700 f64.store)
  (func (export "f32st") i32.const 0x1900 f32.const 1.5 f32.store offset=0x1700)
  (func (export "f64st") i32.const 0x900 f64.const -2.25 f64.store offset=0x1700)
  (func (export "rd2000") (result i32) i32.const 0 i32.load offset=0x2000)
  (func (export "rd2004") (result i32) i32.const 0 i32.load offset=0x2004)
  (func (export "rd3000") (result i32) i32.const 0 i32.load offset=0x3000)
  (func (export "rd3004") (result i32) i32.const 0 i32.load offset=0x3004))"""

# f64 rows avoid returning an f64 through `i64.reinterpret_f64`: that return
# shape is miscompiled independently of --native-pointer-abi (the pair is not
# moved to r0:r1), so the loaded value is stored and read back as i32 words.
FP_SEQ = ["anchor", "f32ld", "f64ld", "rd3000", "rd3004", "f32st", "rd3000",
          "f64st", "rd2000", "rd2004"]

CASES = [("sp", SP, SP_SEQ, "cortex-m3"), ("fp", FP, FP_SEQ, "cortex-m7dp")]

# A header whose stack-pointer init (0x4) is below a same-region offset, so
# the offset alone is relocated too (rule 2) and the local's relocated
# constant would be doubled although C + offset stays in C's region.
HDR_LOW_SP = r"""(module (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x4))
  (data (i32.const 0x900) "\aa\bb\cc\dd\ee\ff\11\22")
"""

REFUSE = [
    ("local_ld", HDR, "(result i32) (local i32) i32.const 0x1900 local.set 0 "
     "local.get 0 i32.load offset=0x704"),
    ("local_tee", HDR, "(result i32) (local i32) i32.const 0x900 local.tee 0 "
     "i32.load offset=0x1704"),
    ("local_i64", HDR, "(result i64) (local i32) i32.const 0x1900 local.set 0 "
     "local.get 0 i64.load offset=0x700"),
    # rule 2 through a local: `v` = 4 is a scalar, the offset 0x1ffc is
    # relocated and retargeted by itself (no segment), +4 lands in 0x2000's.
    ("local_rule2", HDR, "(result i32) (local i32) i32.const 4 local.set 0 "
     "local.get 0 i32.load offset=0x1ffc"),
    # both parts relocated, same region: the address is doubled.
    ("local_double", HDR_LOW_SP, "(result i32) (local i32) i32.const 0x900 "
     "local.set 0 local.get 0 i32.load offset=4"),
]

GARBAGE_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7,
                UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R12]


def poison(linked, k):
    linked.mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)  # CPACR: CP10/CP11
    linked.mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)  # FPEXC.EN
    for i, reg in enumerate(GARBAGE_REGS):
        linked.mu.reg_write(reg, (0xDEAD0000 | (k << 8) | i) & 0xFFFFFFFF)
    sp = h.BASES[".bss"] + h.MAPSZ - 0x100
    linked.mu.mem_write(sp - 0x1000, bytes([0xA5 ^ (k & 0xFF)]) * 0x1000)


def compile_obj(wat, tmp, label, target):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}.o"
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", target,
         "--all-exports", "--relocatable", "--native-pointer-abi"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    log = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0 or "VCR-VER-003" in log:
        print(f"{label}: compile must be CLEAN: rc={r.returncode}\n{log[-1500:]}")
        return None
    return obj


def assert_refusals(tmp):
    bad = 0
    for label, hdr, body in REFUSE:
        src = tmp / f"refuse_{label}.wat"
        src.write_text(hdr + r"""  (func (export "anchor") (result i32) (i32.load (i32.const 0x900)))
  (func (export "f") """ + body + "))")
        obj = tmp / f"refuse_{label}.o"
        r = subprocess.run(
            [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m3",
             "--all-exports", "--relocatable", "--native-pointer-abi"],
            capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
        )
        log = (r.stdout or "") + (r.stderr or "")
        why = None
        if r.returncode == 0:
            why = "compiled with exit 0"
        elif "panicked at" in log:
            why = "refusal PANICKED"
        elif "(#1580)" not in log or "through local 0" not in log:
            why = f"refused for the WRONG reason: {log[-500:]}"
        elif obj.exists() and obj.stat().st_size > 0:
            why = "an object was written despite the refusal"
        print(f"  [{'ok ' if why is None else 'BUG'}] refuse {label}"
              + ("" if why is None else f": {why}"))
        bad += why is not None
    return bad


def main():
    tmp = Path(tempfile.mkdtemp(prefix="npaoff1580_"))
    fails = compared = 0
    for label, wat, seq, target in CASES:
        obj = compile_obj(wat, tmp, label, target)
        if obj is None:
            fails += len(seq)
            continue
        linked = h.Linked(obj)
        engine = wasmtime.Engine()
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
        print(f"=== {label} ({target}, {linked.abs32} static-data ABS32 relocs) ===")
        for k, fn in enumerate(seq):
            func = inst.exports(store)[fn]
            res = func(store)
            ntype = func.type(store).results
            poison(linked, k)
            got = linked.call(fn)
            if isinstance(got, str):
                ok, shown = False, got
            elif not ntype:
                ok, shown, res = True, "(void)", None
            elif str(ntype[0]) == "i64":
                v = got[0] | (got[1] << 32)
                ok, shown = v == res & 0xFFFFFFFFFFFFFFFF, hex(v)
            else:
                ok, shown = got[0] == res & 0xFFFFFFFF, hex(got[0])
            compared += 1
            fails += not ok
            exp = "(void)" if res is None else hex(res & 0xFFFFFFFFFFFFFFFF)
            print(f"  [{'ok ' if ok else 'BUG'}] {fn}() -> {shown}  (wasmtime {exp})")
    if compared == 0:
        print("VACUOUS: compared nothing")
        return 1
    print("=== constant through a local + offset (must be refused, #1580) ===")
    bad_refusals = assert_refusals(tmp)
    print(f"\ncompared: {compared}")
    print(f"refusals: {len(REFUSE) - bad_refusals} of {len(REFUSE)}")
    total = fails + bad_refusals
    print(f"ORACLE: {'PASS' if total == 0 else f'FAIL ({fails} divergences, {bad_refusals} refusal misses)'}")
    return 0 if total == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
