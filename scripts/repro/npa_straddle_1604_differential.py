#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 82
"""#1604 — under --native-pointer-abi a constant access whose bytes span two
data regions is REFUSED; every access inside one region still executes
correctly — execution differential vs wasmtime + refusal matrix.

THE DEFECT. When every data segment sits at or above the static-data base,
the relocatable object's mixed split (#354) is not a contiguous image of
linear memory: the zero-initialised reservation is a `.bss` under
`__synth_wasm_data`, and each segment is packed (4-aligned, declaration
order, then the globals slots) into a `.data` under its own
`__synth_wasm_seg_K`. A relocated address is retargeted by the region of its
FIRST byte, so an access whose bytes `[ea, ea + width)` cross a region
boundary reads or writes the wrong bytes for its tail:

  res->seg   starts in the reservation, runs into a segment: reads the
             reservation's zeros (`i32.const 0x1ffe i32.load`, data at
             0x2000: 0x0, wasmtime 0x32310000 — the issue's row); a store
             writes the `.bss` copy and the segment never changes.
  seg->gap   runs off the end of the LAST packed segment into the globals
             slots: with a stack-pointer global an i32 load reads the SP
             slot (0x08006867), a store CLOBBERS it.
  seg->pad   runs off a segment whose length is not a multiple of 4 into
             its packing padding: loads happen to read 0 (correct by value),
             stores land in the padding and are lost.
  seg->seg   two linmem-adjacent segments — correct today only when they
             are declared consecutively with a 4-multiple length (packed
             adjacency coincides with linmem adjacency); refused, because
             the selector does not re-derive the packer.
  overlap    a later segment overwrites the middle of an earlier one; the
             access starts in the earlier segment's surviving bytes.

VCR-VER-003 checks only retargeted relocations, by VALUE: a reservation
start is outside its population, a store into zero padding passes a byte
comparison, and a relocation whose width is unproven (a pointer constant
under a stack-pointer global, a local) is checked only on covered bytes.

THE FIX (`InstructionSelector::npa_region_straddle_guard`) refuses, before
selection, any memory access whose CONSTANT effective address (the producing
`i32.const` after the #1580 offset fold, or every value of a #1568
constant-only local) touches bytes of two regions, with the same
last-declared-wins region rule the split retargets by. The width is the
access's own, or the constant length of `memory.fill` / `memory.copy`.

ACCEPT (executed, R0-R10/R12 and the stack below SP poisoned before every
call): accesses that END exactly at a region boundary or START exactly at
one — reservation tails, segment heads/tails, a whole segment, a padded
segment's last word, `memory.fill` inside a segment and up to its first
byte — loads, and stores read back BYTE BY BYTE through each byte's own
region (never through the shape that wrote it).

REFUSE (rc != 0, `(#1604)` named, no panic, no object): the five classes
above x const / offset / local address forms x loads and stores x i16 / i32
/ i64 / f32 / f64, plus `memory.fill` / `memory.copy` (destination and
source), plus — with a stack-pointer global — a RUN-TIME base whose memarg
offset is relocated alone (#739) and spans two regions (called with 0 on the
pre-fix binary it reads the reservation the same way). Rows the pre-#1604 compiler already refused for another reason
(no-stack-pointer i64 / float constants, #1568) are excluded.

RED on the pre-fix binary (main d048b523, #1602 merged): exits 1 — every refusal row
compiles with rc 0; the script then executes it and prints the divergence.

NOT covered (named residuals, RQ-89-ZERORESV): a bulk access with a
non-constant length, a constant reached through arithmetic, and a run-time
base whose offset is not relocated (no stack-pointer global, #1568 shape 2)
— no static byte range to check.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/npa_straddle_1604_differential.py
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

# D is declared first and is 6 bytes long, so 2 padding bytes follow it in the
# packed .data; A and B are linmem-adjacent; C is the last packed segment (the
# globals slots follow it); F overwrites the tail of E.
SEGS = r"""  (data (i32.const 0x2800) "\71\72\73\74\75\76")
  (data (i32.const 0x2000) "\31\32\33\34\35\36\37\38")
  (data (i32.const 0x2008) "\41\42\43\44\45\46\47\48")
  (data (i32.const 0x2400) "\51\52\53\54\55\56\57\58")
  (data (i32.const 0x2406) "\61\62")
  (data (i32.const 0x3000) "\61\62\63\64\65\66\67\68")
"""
HDRS = {
    "nosp": '(module (memory (export "mem") 1)\n',
    "sp": '(module (memory (export "mem") 1)\n  (global $sp (mut i32) (i32.const 0x800))\n',
}

# ---------------------------------------------------------------- ACCEPT ----
INT_FUNCS = r"""
  (func (export "res_tail") (result i32) i32.const 0x1ffc i32.load)
  (func (export "a_head") (result i32) i32.const 0x2000 i32.load)
  (func (export "a_tail") (result i32) i32.const 0 i32.load offset=0x2004)
  (func (export "b_head16") (result i32) i32.const 0x2008 i32.load16_u)
  (func (export "c_tail") (result i32) i32.const 0x3004 i32.load)
  (func (export "c_tail16") (result i32) i32.const 0x3006 i32.load16_s)
  (func (export "gap_head") (result i32) i32.const 0x3008 i32.load)
  (func (export "d_tail16") (result i32) i32.const 0x2804 i32.load16_u)
  (func (export "f_word") (result i32) i32.const 0x2406 i32.load16_u)
  (func (export "loc_a_tail") (result i32) (local i32) i32.const 0x2004 local.set 0
    local.get 0 i32.load)
  (func (export "st_res_tail") i32.const 0x1ffc i32.const 0x5a5b5c5d i32.store)
  (func (export "st_a_tail") i32.const 0x2004 i32.const 0x01020304 i32.store)
  (func (export "st_c_tail16") i32.const 0 i32.const 0x7766 i32.store16 offset=0x3006)
  (func (export "st_d_tail16") i32.const 0x2804 i32.const 0x99aa i32.store16)
"""
SP_ONLY_FUNCS = r"""
  (func (export "a_whole64") (result i64) i32.const 0x2000 i64.load)
  (func (export "c_whole64") (result i64) i32.const 0 i64.load offset=0x3000)
  (func (export "st_b_whole64") i32.const 0x2008 i64.const 0x1122334455667788 i64.store)
  (func (export "fill_a") i32.const 0x2002 i32.const 0xee i32.const 4 memory.fill)
  (func (export "fill_res") i32.const 0x1ff0 i32.const 0xcd i32.const 0x10 memory.fill)
"""
BYTES = [0x1ffc, 0x1ffd, 0x1ffe, 0x1fff, 0x2002, 0x2003, 0x2004, 0x2005,
         0x2006, 0x2007, 0x2008, 0x200f, 0x2804, 0x2805, 0x3006, 0x3007]
READBACK = "".join(
    f'  (func (export "b{a:x}") (result i32) i32.const {a:#x} i32.load8_u)\n'
    for a in BYTES)
RB = [f"b{a:x}" for a in BYTES]

INT_SEQ = ["res_tail", "a_head", "a_tail", "b_head16", "c_tail", "c_tail16",
           "gap_head", "d_tail16", "f_word", "loc_a_tail",
           "st_res_tail", "st_a_tail", "st_c_tail16", "st_d_tail16"] + RB
SP_SEQ = INT_SEQ + ["a_whole64", "c_whole64", "st_b_whole64", "b2008", "b200f",
                    "fill_a", "b2002", "b2005", "fill_res", "b1ffc", "b1fff",
                    "a_head"]

FP_FUNCS = r"""
  (func (export "f32_a_tail") (result i32) i32.const 0x2004 f32.load i32.reinterpret_f32)
  (func (export "f32_d_tail") (result i32) i32.const 0 f32.load offset=0x2802 i32.reinterpret_f32)
  (func (export "f64_c") i32.const 0x1000 i32.const 0x3000 f64.load f64.store)
  (func (export "rd1000") (result i32) i32.const 0x1000 i32.load)
  (func (export "rd1004") (result i32) i32.const 0x1004 i32.load)
  (func (export "f32_st_res") i32.const 0x1ffc f32.const 1.5 f32.store)
  (func (export "f64_st_b") i32.const 0x2008 f64.const -2.25 f64.store)
  (func (export "rd1ffc") (result i32) i32.const 0x1ffc i32.load)
  (func (export "rd2008") (result i32) i32.const 0x2008 i32.load)
  (func (export "rd200c") (result i32) i32.const 0x200c i32.load)
"""
FP_SEQ = ["f32_a_tail", "f32_d_tail", "f64_c", "rd1000", "rd1004",
          "f32_st_res", "rd1ffc", "f64_st_b", "rd2008", "rd200c"]

ACCEPT = [
    ("nosp", HDRS["nosp"] + SEGS + INT_FUNCS + READBACK + ")", INT_SEQ, "cortex-m3"),
    ("sp", HDRS["sp"] + SEGS + INT_FUNCS + SP_ONLY_FUNCS + READBACK + ")", SP_SEQ,
     "cortex-m3"),
    ("sp_fp", HDRS["sp"] + SEGS + FP_FUNCS + ")", FP_SEQ, "cortex-m7dp"),
]

# ---------------------------------------------------------------- REFUSE ----
# class -> effective address for an access of width w
CLASSES = {
    "res_seg": lambda w: 0x2000 - w // 2,
    "seg_gap": lambda w: 0x3008 - w // 2,
    "seg_pad": lambda w: 0x2806 - w // 2,
    "seg_seg": lambda w: 0x2008 - w // 2,
    "overlap": lambda w: 0x2406 - w // 2,
}
# (name, width, kind, op text, target, needs a stack-pointer global for the
# const/offset forms: without one the pre-#1604 compiler already refuses a
# constant address on these arms, #1568)
ACCESSES = [
    ("i32_ld", 4, "ld", "i32.load", "cortex-m3", False),
    ("i16_ld", 2, "ld", "i32.load16_u", "cortex-m3", False),
    ("i32_st", 4, "st", "i32.store", "cortex-m3", False),
    ("i16_st", 2, "st", "i32.store16", "cortex-m3", False),
    ("i64_ld", 8, "ld", "i64.load", "cortex-m3", True),
    ("i64_st", 8, "st", "i64.store", "cortex-m3", True),
    ("f32_ld", 4, "ld", "f32.load", "cortex-m7dp", True),
    ("f64_st", 8, "st", "f64.store", "cortex-m7dp", True),
]
STORE_VALUE = {"i32.store": "i32.const 0x5a5b5c5d", "i32.store16": "i32.const 0x7766",
               "i64.store": "i64.const 0x0102030405060708",
               "f64.store": "f64.const -2.25"}
RESULT = {"i32.load": "i32", "i32.load16_u": "i32", "i64.load": "i64",
          "f32.load": "i32"}


def refuse_rows():
    rows = []
    for hd in HDRS:
        for cls, eff_of in CLASSES.items():
            for aname, w, kind, op, tgt, needs_sp in ACCESSES:
                for form in ("const", "offset", "local", "runtime"):
                    if hd == "nosp" and needs_sp and form not in ("local",):
                        continue
                    if hd == "nosp" and form == "runtime":
                        continue  # not relocated without an SP global (#1568)
                    ea = eff_of(w)
                    if form == "const":
                        push, mem, loc = f"i32.const {ea:#x}", op, ""
                    elif form == "offset":
                        push, mem, loc = "i32.const 0", f"{op} offset={ea:#x}", ""
                    elif form == "runtime":
                        # a run-time base (called with 0): the offset is
                        # relocated alone (#739) and retargeted by its region
                        push, mem, loc = "local.get 0", f"{op} offset={ea:#x}", "(param i32) "
                    else:
                        push = f"i32.const {ea:#x} local.set 0 local.get 0"
                        mem, loc = op, "(local i32) "
                    if op == "f32.load":
                        mem += " i32.reinterpret_f32"
                    if kind == "ld" and form == "runtime":
                        body = f"{loc}(result {RESULT[op]}) {push} {mem}"
                    elif kind == "ld":
                        body = f"(result {RESULT[op]}) {loc}{push} {mem}"
                    else:
                        body = f"{loc}{push} {STORE_VALUE[op]} {mem}"
                    rb = "".join(
                        f'  (func (export "b{i}") (result i32) i32.const {ea + i:#x} i32.load8_u)\n'
                        for i in range(w))
                    seq = ["f"] + ([f"b{i}" for i in range(w)] if kind == "st" else [])
                    rows.append((f"{hd}/{cls}/{form}/{aname}",
                                 HDRS[hd] + SEGS + f'  (func (export "f") {body})\n' + rb + ")",
                                 seq, tgt))
        if hd == "sp":
            for cls, eff_of in CLASSES.items():
                ea = eff_of(4)
                for bname, text in (
                        ("fill", f"i32.const {ea:#x} i32.const 0x5a i32.const 4 memory.fill"),
                        ("copy_dst", f"i32.const {ea:#x} i32.const 0x1000 i32.const 4 memory.copy"),
                        ("copy_src", f"i32.const 0x1000 i32.const {ea:#x} i32.const 4 memory.copy")):
                    rb = "".join(
                        f'  (func (export "b{i}") (result i32) i32.const {a:#x} i32.load8_u)\n'
                        for i, a in enumerate([ea + k for k in range(4)]
                                              + [0x1000 + k for k in range(4)]))
                    rows.append((f"sp/{cls}/bulk/{bname}",
                                 HDRS["sp"] + SEGS + f'  (func (export "f") {text})\n' + rb + ")",
                                 ["f"] + [f"b{i}" for i in range(8)], "cortex-m3"))
    return rows


GARBAGE_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7,
                UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R12]


def poison(linked, k):
    linked.mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)  # CPACR: CP10/CP11
    linked.mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)  # FPEXC.EN
    for i, reg in enumerate(GARBAGE_REGS):
        linked.mu.reg_write(reg, (0xDEAD0000 | ((k & 0xFF) << 8) | i) & 0xFFFFFFFF)
    sp = h.BASES[".bss"] + h.MAPSZ - 0x100
    linked.mu.mem_write(sp - 0x1000, bytes([0xA5 ^ (k & 0xFF)]) * 0x1000)


def compile_obj(wat, tmp, label, target):
    src = tmp / f"{label.replace('/', '_')}.wat"
    src.write_text(wat)
    obj = tmp / f"{label.replace('/', '_')}.o"
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", target,
         "--all-exports", "--relocatable", "--native-pointer-abi"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    return r.returncode, (r.stdout or "") + (r.stderr or ""), obj


def differential(obj, wat, seq, verbose):
    """Execute `seq` on synth's object and on wasmtime; return the divergences."""
    linked = h.Linked(obj)
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
    bad = []
    for k, fn in enumerate(seq):
        func = inst.exports(store)[fn]
        nparams = len(func.type(store).params)
        res = func(store, *([0] * nparams))
        ntype = func.type(store).results
        poison(linked, k)
        for reg in GARBAGE_REGS[:nparams]:  # a run-time base of 0
            linked.mu.reg_write(reg, 0)
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
        exp = "(void)" if res is None else hex(res & 0xFFFFFFFFFFFFFFFF)
        if verbose:
            print(f"  [{'ok ' if ok else 'BUG'}] {fn}() -> {shown}  (wasmtime {exp})")
        if not ok:
            bad.append(f"{fn}() -> {shown}, wasmtime {exp}")
    return bad


def main():
    tmp = Path(tempfile.mkdtemp(prefix="npastraddle1604_"))
    fails = compared = 0
    for label, wat, seq, target in ACCEPT:
        rc, log, obj = compile_obj(wat, tmp, label, target)
        if rc != 0 or "VCR-VER-003" in log:
            print(f"{label}: compile must be CLEAN: rc={rc}\n{log[-1500:]}")
            fails += len(seq)
            continue
        print(f"=== accept {label} ({target}) ===")
        bad = differential(obj, wat, seq, True)
        compared += len(seq)
        fails += len(bad)
    if compared == 0:
        print("VACUOUS: compared nothing")
        return 1

    rows = refuse_rows()
    print(f"=== straddling accesses (must be refused, #1604): {len(rows)} rows ===")
    refused = 0
    misses = []
    for label, wat, seq, target in rows:
        rc, log, obj = compile_obj(wat, tmp, label, target)
        why = None
        if rc == 0:
            bad = differential(obj, wat, seq, False)
            why = ("compiled with exit 0; executed: "
                   + (bad[0] if bad else "agrees with wasmtime on this harness"))
        elif "panicked at" in log:
            why = "refusal PANICKED"
        elif "(#1604)" not in log or "which span" not in log:
            why = f"refused for the WRONG reason: {log.strip().splitlines()[-1][:200]}"
        elif obj.exists() and obj.stat().st_size > 0:
            why = "an object was written despite the refusal"
        if why is None:
            refused += 1
        else:
            misses.append(f"  [BUG] {label}: {why}")
    for m in misses:
        print(m)
    print(f"\ncompared: {compared}")
    print(f"refusals: {refused} of {len(rows)}")
    total = fails + len(misses)
    print(f"ORACLE: {'PASS' if total == 0 else f'FAIL ({fails} divergences, {len(misses)} refusal misses)'}")
    return 0 if total == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
