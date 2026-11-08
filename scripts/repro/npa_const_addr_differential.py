#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 65
"""--native-pointer-abi never bakes a constant static address as a raw
linear-memory offset off R11 — execution differential vs wasmtime.

Under `--native-pointer-abi` R11 is 0 (`CompileConfig::linear_memory_bytes`:
"any address beyond it is a runtime host pointer -> `[R11=0 + addr]`"; the
CLI flag doc's "linmem base = 0"), so a wasm static is reachable ONLY through
the `__synth_wasm_data + C` relocation, retargeted to `__synth_wasm_seg_K` on
the mixed split. Before this fix the selector relocated a constant address
only (a) when a stack-pointer global marked the constant a pointer, (b) for a
memarg offset in the static region (also stack-pointer-gated) or (c) through
the i32 const-address fold, which stopped at the 0xFFF imm12 limit. Every
other constant address was emitted as `movw rX,#addr; ldr [fp, rX]` — reading
absolute address `addr`, not the static. A module with NO stack-pointer
global therefore read wrong bytes for every constant address above 0xFFF, and
for every constant address on the i64 / f32 / f64 / memory.fill /
memory.copy arms, silently (measured at the pre-fix binary: 81 of 162 probe
modules wrong, 0 refused for that reason).

The fix extends (c) to any static address the access would otherwise bake,
and REFUSES loudly the arms that cannot fold. This oracle executes the
relocated shapes against wasmtime (hand-linked, .text/.data/.bss at separate
bases, R11 = 0, one instance per case so a store is observed by the loads
after it) and asserts that every non-folding arm is refused with the precise
diagnostic and no object written.

  nosp       — two segments, no stack-pointer global: a folded low load plus
               loads/stores at 0x1004, 0x1007 and `i32.const 0; offset=0x1000`.
  multi_seg  — scripts/repro/multi_segment_static_data.wat on the mixed split
               (its b_after / d_* / gap exports were wrong before the fix).
  sliver     — WITH a stack-pointer global (0x2000): `i32.const 0x1800
               offset=0x1000`, where neither part is a pointer on its own.
  local      — RQ-89-NPARESIDUE (#1568) shape 1, no stack-pointer global: a
               constant pointer routed through a local
               (`i32.const 0x1004 local.set 0 local.get 0 i32.load`, plus the
               tee / store / byte / i64 twins and a low 0x100 address). The
               local is read only as an exact scalar address, so its constant
               is relocated where it is defined. All 7 rows were WRONG at
               0161dee1 (each faulted on the unmapped absolute address).
  local_sp   — the same through a local WITH a stack-pointer global (0x800):
               already relocated by the #237 rule; no-regression rows.

The refusal half also asserts, for the local-routed shape, one row per
condition the relocation needs (memarg offset 0, a set before every read, no
scalar observer, and the stack-pointer sliver reached through a local).

SHAPE 2 (RQ-90-NPASHAPE2, #1568): a DYNAMIC access — a base computed at run
time — whose memarg offset lands in the module's static region, in a module
with no stack-pointer global (none with a positive init). The offset is
emitted raw off R11 = 0, so `(i32.load offset=0x1000 (local.get 0))` over a
segment at 0x1000 dereferences absolute 0x1000 (measured at c20d37b2: rc 0,
dyn(0) faults on an unmapped read, wasmtime 0x44332211). The maintainer's and
gale's decision is a LOUD MODULE-LEVEL REFUSAL: the static region is
[lowest active data segment of memory 0, memory 0's declared minimum size),
an access is named when the bytes it touches intersect it, and the compile
exits non-zero with no object, `--allow-skipped-exports` or not. Asserted
here:
  shape2 refusals — one row per dynamic-base kind (parameter, global,
               arithmetic, a local with a non-constant definition, an
               internal helper reached only by a call) and per access family
               and edge (i32/i64/f32 load, i32 store, the last byte of the
               region, a 4-byte access straddling into it). Each must name the
               function, the offset and the region bounds, carry the
               `npa-dynamic-static-offset (#1568)` needle and NOT the
               constant-address guard's, write no object, and do so twice:
               plain and with --allow-skipped-exports.
  shape2_near  — the NEAR MISS, executed: the same module with offsets that
               stop just below the region (0xFFC i32, 0xFFF u8, 0xFF8 i64)
               compiles and matches wasmtime, plus an offset AT the region's
               upper bound (0x10000) that compiles. EMULATION OF THE
               NATIVE-POINTER CONTRACT for these rows: R11 = 0 and the base is
               a native address, so `base + offset` with base 0 is absolute;
               unicorn maps [0, 0x1000) zero-filled — exactly wasmtime's
               memory below the first segment — and leaves the region itself
               unmapped, so a store then a load through it is observed.
  shape2_sp    — the same dynamic accesses WITH a stack-pointer global
               (0x800): the offset is relocated by the #739 rule, so the
               refusal must NOT fire; executed against wasmtime.

NOT covered, and not catchable by these rules:
  - a dynamic access whose OFFSET sits below the first data segment but whose
    base carries it into the statics, or any dynamic access in a module with
    no active data segment (BSS-only) — synth cannot tell a host-pointer base
    from a wasm-offset base, which is why shape 2 is refused rather than fixed;
  - WITH a stack-pointer global, a dynamic offset into data that sits BELOW
    the stack pointer's init (the #739 rule relocates offsets at or above it);
  - a constant address reaching the access through arithmetic, or through a
    local that also has a non-constant definition.
They still read the wrong address; they are reported, not pinned.
(WITH a stack-pointer global, a relocated pointer constant plus a non-zero
memarg offset that leaves the constant's region — found by this lane — is
relocated on the effective address or refused since #1580:
scripts/repro/npa_offset_cross_segment_1580_differential.py.)

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/npa_const_addr_differential.py
Exits nonzero on any mismatch or missing refusal.
"""

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_C1_C0_2,
    UC_ARM_REG_FPEXC,
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
R_ARM_ABS32 = 2
R_ARM_THM_CALL = 10
BASES = {".text": 0x10000, ".data": 0x60000, ".bss": 0x80000}
MAPSZ = 0x20000

HERE = Path(__file__).parent
HERE = Path(__file__).parent
NOSP = r"""(module
  (memory (export "mem") 1)
  (data (i32.const 0x100) "\aa\bb\cc\dd")
  (data (i32.const 0x1000) "\11\22\33\44\55\66\77\88")
  (func (export "low") (result i32) (i32.load (i32.const 0x100)))
  (func (export "high") (result i32) (i32.load (i32.const 0x1004)))
  (func (export "high8") (result i32) (i32.load8_u (i32.const 0x1007)))
  (func (export "high_off") (result i32) (i32.load offset=0x1000 (i32.const 0)))
  (func (export "set_high") (i32.store (i32.const 0x1000) (i32.const 0x5a5a5a5a)))
  (func (export "set_high8") (i32.store8 (i32.const 0x1001) (i32.const 0x77))))"""

SLIVER = r"""(module
  (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x2000))
  (data (i32.const 0x2800) "\31\32\33\34\35\36\37\38")
  (func (export "ld") (result i32) i32.const 0x1800 i32.load offset=0x1000)
  (func (export "ld16") (result i32) i32.const 0x1800 i32.load16_s offset=0x1002)
  (func (export "st8") i32.const 0x1800 i32.const 0x99 i32.store8 offset=0x1001)
  (func (export "st") i32.const 0x1800 i32.const 0x01020304 i32.store offset=0x1004))"""

LOCAL = r"""(module
  (memory (export "mem") 1)
  (data (i32.const 0x100) "\aa\bb\cc\dd")
  (data (i32.const 0x1000) "\11\22\33\44\55\66\77\88")
  (func (export "anchor") (result i32) (i32.load (i32.const 0x100)))
  (func (export "ld") (result i32) (local i32) i32.const 0x1004 local.set 0 local.get 0 i32.load)
  (func (export "ld_low") (result i32) (local i32) i32.const 0x100 local.set 0 local.get 0 i32.load)
  (func (export "ld8") (result i32) (local i32) i32.const 0x1005 local.set 0 local.get 0 i32.load8_u)
  (func (export "tee") (result i32) (local i32) i32.const 0x1004 local.tee 0 i32.load)
  (func (export "st") (local i32) i32.const 0x1000 local.set 0 local.get 0 i32.const 0x5a5a5a5a i32.store)
  (func (export "ld0") (result i32) (local i32) i32.const 0x1000 local.set 0 local.get 0 i32.load)
  (func (export "ld64") (result i64) (local i32) i32.const 0x1000 local.set 0 local.get 0 i64.load))"""

LOCAL_SP = r"""(module
  (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x800))
  (data (i32.const 0x1000) "\11\22\33\44\55\66\77\88")
  (func (export "ld") (result i32) (local i32) i32.const 0x1004 local.set 0 local.get 0 i32.load)
  (func (export "st") (local i32) i32.const 0x1000 local.set 0 local.get 0 i32.const 0x5a5a5a5a i32.store)
  (func (export "ld0") (result i32) (local i32) i32.const 0x1000 local.set 0 local.get 0 i32.load))"""

CASES = [
    ("nosp", NOSP, ["low", "high", "high8", "high_off", "set_high", "high",
                    "set_high8", "high8", "low"]),
    ("multi_seg", (HERE / "multi_segment_static_data.wat").read_text(),
     ["a_lo", "a_hi", "b_straddle", "b_after", "c_head", "c_ovl", "d_lo",
      "d_hi", "d_byte", "e_0", "e_16", "e_28", "gap"]),
    ("sliver", SLIVER, ["ld", "ld16", "st8", "ld", "st", "ld16"]),
    ("local", LOCAL, ["ld", "ld_low", "ld8", "tee", "st", "ld0", "ld64"]),
    ("local_sp", LOCAL_SP, ["ld", "st", "ld0"]),
]

# Arms that cannot fold a constant address. Before RQ-91-NPAMODEL each was
# REFUSED per function by the selector's constant-address guard. The
# module-level memory-0 decision now RELOCATES the constant at its definition
# (`__synth_wasm_data + C`), so the non-folding arms compile — and are
# EXECUTED against wasmtime below (RELOCATED); the shapes it cannot relocate
# soundly stay refused, each with the named diagnostic in its row (REFUSE).
# Every module carries the folded `anchor` so the region is referenced and
# the #1041 refusal cannot be what fires.
REFUSE_HDR = r"""(module (memory (export "mem") 1)
  (data (i32.const 0x100) "\01\02\03\04\05\06\07\08")
  (data (i32.const 0x1000) "\11\12\13\14\15\16\17\18")
  (func (export "anchor") (result i32) (i32.load (i32.const 0x100)))
  (func (export "f") """
# Relocated now (were refused): (label, target, function body, call sequence).
# The read-back exports observe what a store / fill / copy wrote.
READBACK = r"""
  (func (export "r100") (result i32) (i32.load (i32.const 0x100)))
  (func (export "r104") (result i32) (i32.load (i32.const 0x104)))
  (func (export "r1000") (result i32) (i32.load (i32.const 0x1000)))
  (func (export "r1004") (result i32) (i32.load (i32.const 0x1004)))"""
RELOCATED = [
    ("i64_load", "(result i64) i32.const 0x1000 i64.load", ["f"]),
    ("i64_load_low", "(result i64) i32.const 0x100 i64.load", ["f"]),
    ("i64_store", "i32.const 0x1000 i64.const 7 i64.store", ["f", "r1000", "r1004"]),
    ("i64_load8", "(result i64) i32.const 0x1001 i64.load8_u", ["f"]),
    ("f32_store", "i32.const 0x1000 f32.const 1 f32.store", ["f", "r1000", "r1004"],
     "cortex-m7dp"),
    ("memory_fill", "i32.const 0x1000 i32.const 9 i32.const 4 memory.fill",
     ["f", "r1000", "r1004"]),
    ("memory_copy_src", "i32.const 0x104 i32.const 0x1000 i32.const 4 memory.copy",
     ["f", "r100", "r104"]),
    # f64.load from a constant static: read and stored back to 0x100 (an f64
    # result would come back in D0, which this harness does not read).
    ("f64_load", "i32.const 0x100 i32.const 0x1000 f64.load f64.store",
     ["f", "r100", "r104"], "cortex-m7dp"),
]
# Still refused: (label, target, function body, the diagnostic it must carry).
REFUSE = [
    # RQ-89-NPARESIDUE (#1568) shape 1: a constant routed through a local the
    # decision cannot relocate soundly — one row per condition.
    ("local_nonzero_offset", "cortex-m3",
     "(result i32) (local i32) i32.const 5 local.set 0 local.get 0 "
     "i32.load8_u offset=0x1000", "npa-region-straddle (#1604)"),
    ("local_zero_init_visible", "cortex-m3",
     "(result i32) (local i32) block i32.const 0x1004 local.set 0 end "
     "local.get 0 i32.load", "npa-static-unrelocatable (#1568)"),
    ("local_scalar_observer", "cortex-m3",
     "(result i32) (local i32) i32.const 0x1004 local.set 0 local.get 0 "
     "i32.load local.get 0 i32.add", "npa-static-observed (#1568)"),
    ("local_i64_nonzero_offset", "cortex-m3",
     "(result i64) (local i32) i32.const 0x1000 local.set 0 local.get 0 "
     "i64.load offset=4", "npa-region-straddle (#1604)"),
]
# The stack-pointer sliver reached through a local (header with an SP global).
REFUSE_SP_HDR = r"""(module (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x2000))
  (data (i32.const 0x2800) "\31\32\33\34\35\36\37\38")
  (func (export "anchor") (result i32) (i32.load (i32.const 0x2800)))
  (func (export "f") """
REFUSE_SP = [
    ("local_sp_sliver", "cortex-m3",
     "(result i32) (local i32) i32.const 0x1800 local.set 0 local.get 0 "
     "i32.load offset=0x1000", "npa-static-unrelocatable (#1568)"),
]
# The retired per-shape guard's text: no diagnostic may carry it any more.
NEEDLE = "which this lowering would emit as a raw linear-memory offset off R11"

# RQ-90-NPASHAPE2 (#1568 shape 2). One segment at 0x1000 in a one-page memory:
# the static region is [0x1000, 0x10000).
S2_SEG = r"""(module (memory (export "mem") 1)
  (data (i32.const 0x1000) "\11\22\33\44\55\66\77\88")
  (func (export "anchor") (result i32) (i32.load (i32.const 0x1000)))
"""
S2_NEEDLE = "npa-dynamic-static-offset (#1568)"
S2_REGION = "[0x1000, 0x10000)"
# (label, target, extra module text, named function, offset)
S2_REFUSE = [
    ("param_i32_load", "cortex-m3",
     '(func (export "f") (param i32) (result i32) local.get 0 i32.load offset=0x1000)',
     "f", 0x1000),
    ("param_i32_store", "cortex-m3",
     '(func (export "f") (param i32) local.get 0 i32.const 7 i32.store offset=0x1004)',
     "f", 0x1004),
    ("param_i64_load", "cortex-m3",
     '(func (export "f") (param i32) (result i64) local.get 0 i64.load offset=0x1000)',
     "f", 0x1000),
    ("param_f32_load", "cortex-m7dp",
     '(func (export "f") (param i32) (result f32) local.get 0 f32.load offset=0x1000)',
     "f", 0x1000),
    ("region_last_byte", "cortex-m3",
     '(func (export "f") (param i32) (result i32) local.get 0 i32.load8_u offset=0xffff)',
     "f", 0xFFFF),
    ("straddle_into_region", "cortex-m3",
     '(func (export "f") (param i32) (result i32) local.get 0 i32.load offset=0xffd)',
     "f", 0xFFD),
    ("global_base", "cortex-m3",
     '(global $g (mut i32) (i32.const 0)) '
     '(func (export "f") (result i32) global.get $g i32.load offset=0x1000)',
     "f", 0x1000),
    ("arith_base", "cortex-m3",
     '(func (export "f") (param i32) (result i32) local.get 0 i32.const 4 i32.add '
     'i32.load offset=0x1000)',
     "f", 0x1000),
    ("nonconst_local_base", "cortex-m3",
     '(func (export "f") (param i32) (result i32) (local i32) local.get 0 local.set 1 '
     'local.get 1 i32.load offset=0x1000)',
     "f", 0x1000),
    ("internal_helper", "cortex-m3",
     '(func $h (param i32) (result i32) local.get 0 i32.load offset=0x1000) '
     # RQ-91-NPAMODEL: the base reaches the helper from the HOST (an export
     # parameter). With `i32.const 0 call $h` the module-level provenance
     # pass sees the constant through the call and refuses the constant
     # address as a straddle instead — still refused, under another name.
     '(func (export "f") (param i32) (result i32) local.get 0 call $h)',
     "func_1", 0x1000),
]
S2_NEAR = S2_SEG + r"""  (func (export "nm_ld") (param i32) (result i32) local.get 0 i32.load offset=0xffc)
  (func (export "nm_st") (param i32 i32) local.get 0 local.get 1 i32.store offset=0xffc)
  (func (export "nm_ld8") (param i32) (result i32) local.get 0 i32.load8_u offset=0xfff)
  (func (export "nm_ld64") (param i32) (result i64) local.get 0 i64.load offset=0xff8)
  (func (export "nm_hi") (param i32) (result i32) local.get 0 i32.load offset=0x10000))"""
S2_NEAR_SEQ = [("nm_ld", (0,)), ("nm_st", (0, 0x5A5A1234)), ("nm_ld", (0,)),
               ("nm_ld8", (0,)), ("nm_ld64", (0,))]
S2_SP = r"""(module (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x800))
  (data (i32.const 0x1000) "\11\22\33\44\55\66\77\88")
  (func (export "anchor") (result i32) (i32.load (i32.const 0x1000)))
  (func (export "ld") (param i32) (result i32) local.get 0 i32.load offset=0x1000)
  (func (export "st") (param i32) local.get 0 i32.const 0x01020304 i32.store offset=0x1004)
  (func (export "ld64") (param i32) (result i64) local.get 0 i64.load offset=0x1000))"""
S2_SP_SEQ = [("ld", (0,)), ("st", (0,)), ("ld64", (0,)), ("ld", (0,))]


def assert_shape2_refusals(tmp):
    """Every S2_REFUSE row is refused for the whole module, twice."""
    n = 0
    for label, tgt, funcs, fname, off in S2_REFUSE:
        src = tmp / f"s2_{label}.wat"
        src.write_text(S2_SEG + funcs + ")")
        for extra in ([], ["--allow-skipped-exports"]):
            obj = tmp / f"s2_{label}{'_ase' if extra else ''}.o"
            r = subprocess.run(
                [SYNTH, "compile", str(src), "-o", str(obj), "--target", tgt,
                 "--all-exports", "--relocatable", "--native-pointer-abi", *extra],
                capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
            )
            log = (r.stdout or "") + (r.stderr or "")
            tag = f"shape2 {label}{' +allow-skipped-exports' if extra else ''}"
            if r.returncode == 0:
                sys.exit(f"{tag}: compiled with exit 0 — a dynamic access whose "
                         f"memarg offset lands in the static region must refuse")
            if "panicked at" in log:
                sys.exit(f"{tag}: refusal PANICKED: {log[-400:]}")
            want = [S2_NEEDLE, f"function '{fname}'", f"offset 0x{off:x}", S2_REGION]
            missing = [w for w in want if w not in log]
            if missing or NEEDLE in log:
                sys.exit(f"{tag}: wrong diagnostic (missing {missing}, "
                         f"constant-guard needle {NEEDLE in log}):\n{log[-900:]}")
            if obj.exists():
                sys.exit(f"{tag}: an object was written despite the refusal")
            print(f"  [ok ] refused: {tag}")
            n += 1
    return n


def run_shape2(tmp, label, wat, seq, low_map, target="cortex-m3"):
    """Execute `seq` (fn, args) in one instance each side; return fails."""
    obj = compile_obj(wat, tmp, label, target)
    linked = Linked(obj, low_map=low_map)
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
    print(f"=== {label} ({linked.abs32} static-data ABS32 relocs) ===")
    fails = 0
    for fn, args in seq:
        func = inst.exports(store)[fn]
        res = func(store, *args)
        ntype = func.type(store).results
        got = linked.call(fn, args)
        if isinstance(got, str):
            ok, shown = False, got
        elif not ntype:
            ok, shown, res = True, "(void)", None
        elif str(ntype[0]) == "i64":
            v = got[0] | (got[1] << 32)
            ok, shown = v == res & 0xFFFFFFFFFFFFFFFF, hex(v)
        else:
            ok, shown = got[0] == res & 0xFFFFFFFF, hex(got[0])
        fails += not ok
        exp = "(void)" if res is None else hex(res & 0xFFFFFFFFFFFFFFFF)
        print(f"  [{'ok ' if ok else 'BUG'}] {fn}{args} -> {shown}  (wasmtime {exp})")
    return fails, len(seq)


def assert_refusals(tmp):
    n = 0
    rows = [(REFUSE_HDR, r) for r in REFUSE] + [(REFUSE_SP_HDR, r) for r in REFUSE_SP]
    for hdr, (label, tgt, body, want) in rows:
        src = tmp / f"refuse_{label}.wat"
        src.write_text(hdr + body + "))")
        obj = tmp / f"refuse_{label}.o"
        r = subprocess.run(
            [SYNTH, "compile", str(src), "-o", str(obj), "--target", tgt,
             "--all-exports", "--relocatable", "--native-pointer-abi"],
            capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
        )
        log = (r.stdout or "") + (r.stderr or "")
        if r.returncode == 0:
            sys.exit(f"refuse {label}: compiled with exit 0 — this shape must be refused")
        if "panicked at" in log:
            sys.exit(f"refuse {label}: refusal PANICKED: {log[-400:]}")
        if want not in log or NEEDLE in log:
            sys.exit(f"refuse {label}: refused for the WRONG reason (want {want!r}):\n"
                     f"{log[-800:]}")
        if obj.exists() and obj.stat().st_size > 0:
            sys.exit(f"refuse {label}: an object was written despite the refusal")
        print(f"  [ok ] refused: {label}")
        n += 1
    return n


def compile_obj(wat_text, tmp, label, target="cortex-m3"):
    src = tmp / f"{label}.wat"
    src.write_text(wat_text)
    obj = tmp / f"{label}.o"
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", target,
         "--all-exports", "--relocatable", "--native-pointer-abi"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    log = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0 or "VCR-VER-003" in log:
        sys.exit(f"{label}: compile must be CLEAN: "
                 f"rc={r.returncode}\n{log[-1500:]}")
    return obj


def thm_bl(src, dst):
    """Encode a Thumb-2 BL from `src` (the instruction address) to `dst`."""
    off = dst - (src + 4)
    if not -(1 << 24) <= off < (1 << 24):
        sys.exit(f"BL out of range: {off:#x}")
    imm = (off >> 1) & 0xFFFFFF
    s = (imm >> 23) & 1
    i1 = (imm >> 22) & 1
    i2 = (imm >> 21) & 1
    j1 = (~(i1 ^ s)) & 1
    j2 = (~(i2 ^ s)) & 1
    hw1 = 0xF000 | (s << 10) | ((imm >> 11) & 0x3FF)
    hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | (imm & 0x7FF)
    return struct.pack("<HH", hw1, hw2)


class Linked:
    def __init__(self, obj, low_map=0):
        e = ELFFile(open(obj, "rb"))
        secs = list(e.iter_sections())
        names = {i: s.name for i, s in enumerate(secs)}
        self.text = bytearray(e.get_section_by_name(".text").data())
        data = e.get_section_by_name(".data")
        self.data = bytes(data.data()) if data is not None else b""
        bss = e.get_section_by_name(".bss")
        self.bss_size = bss["sh_size"] if bss is not None else 0
        for name, size in ((".text", len(self.text)), (".data", len(self.data)),
                           (".bss", self.bss_size)):
            if size > MAPSZ - 0x200:
                sys.exit(f"{name} is {size} B — larger than the harness map")
        symtab = [s for s in secs if s["sh_type"] == "SHT_SYMTAB"][0]
        self.syms = {}
        for s in symtab.iter_symbols():
            if s.name and s["st_shndx"] not in ("SHN_UNDEF", "SHN_ABS"):
                self.syms[s.name] = BASES.get(names[s["st_shndx"]], None), s["st_value"]
        rel = e.get_section_by_name(".rel.text")
        self.abs32 = 0
        for r in rel.iter_relocations() if rel is not None else []:
            sym = symtab.get_symbol(r["r_info_sym"])
            if sym.name not in self.syms or self.syms[sym.name][0] is None:
                sys.exit(f"unresolvable reloc target {sym.name!r}")
            base, val = self.syms[sym.name]
            where = r["r_offset"]
            if r["r_info_type"] == R_ARM_ABS32:
                (add,) = struct.unpack_from("<I", self.text, where)
                struct.pack_into("<I", self.text, where, (base + val + add) & 0xFFFFFFFF)
                self.abs32 += 1
            elif r["r_info_type"] == R_ARM_THM_CALL:
                dst = (base + val) & ~1
                self.text[where:where + 4] = thm_bl(BASES[".text"] + where, dst)
            else:
                sys.exit(f"unhandled reloc type {r['r_info_type']} for {sym.name}")
        if self.abs32 == 0:
            sys.exit("VACUOUS: no R_ARM_ABS32 static-data relocation in the object")
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for base in BASES.values():
            self.mu.mem_map(base, MAPSZ)
        if low_map:
            # Shape 2 near miss: absolute [0, low_map) zero-filled (see above).
            self.mu.mem_map(0, low_map)
        self.mu.mem_write(BASES[".text"], bytes(self.text))
        self.mu.mem_write(BASES[".data"], self.data)
        self.ret = BASES[".text"] + MAPSZ - 0x10
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")
        # The FPU on (CPACR CP10/CP11, FPEXC.EN), for the cortex-m7dp rows;
        # an integer-only object never touches either register.
        self.mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
        self.mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)

    def call(self, fn, args=()):
        if fn not in self.syms:
            return f"ERR:symbol {fn} missing"
        base, val = self.syms[fn]
        for reg, a in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
            self.mu.reg_write(reg, a & 0xFFFFFFFF)
        self.mu.reg_write(UC_ARM_REG_R11, 0)  # native deref
        self.mu.reg_write(UC_ARM_REG_SP, BASES[".bss"] + MAPSZ - 0x100)
        self.mu.reg_write(UC_ARM_REG_LR, self.ret | 1)
        try:
            self.mu.emu_start((base + val) | 1, self.ret, timeout=5_000_000)
        except UcError as ex:
            return f"ERR:{ex}"
        lo = self.mu.reg_read(UC_ARM_REG_R0)
        hi = self.mu.reg_read(UC_ARM_REG_R1)
        return lo, hi


def main():
    tmp = Path(tempfile.mkdtemp(prefix="verwidth1563_"))
    fails = 0
    compared = 0
    for label, wat, seq in CASES:
        obj = compile_obj(wat, tmp, label)
        linked = Linked(obj)
        engine = wasmtime.Engine()
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
        print(f"=== {label} ({linked.abs32} static-data ABS32 relocs) ===")
        for fn in seq:
            func = inst.exports(store)[fn]
            res = func(store)
            ntype = func.type(store).results
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
    # RQ-90-NPASHAPE2 (#1568 shape 2): near miss + stack-pointer twin,
    # executed; then the module-level refusal rows.
    for label, wat, seq, low in (("shape2_near", S2_NEAR, S2_NEAR_SEQ, 0x1000),
                                 ("shape2_sp", S2_SP, S2_SP_SEQ, 0)):
        f, c = run_shape2(tmp, label, wat, seq, low)
        fails += f
        compared += c
    print("=== shape 2: dynamic offset in the static region (must be refused) ===")
    s2 = assert_shape2_refusals(tmp)
    if s2 != 2 * len(S2_REFUSE):
        print(f"VACUOUS: shape-2 refusals={s2} of {2 * len(S2_REFUSE)}")
        return 1
    print(f"shape-2 refusals: {s2}")
    print("=== non-folding arms, relocated at the definition (RQ-91-NPAMODEL) ===")
    for label, body, seq, *tgt in RELOCATED:
        wat = REFUSE_HDR + body + ")" + READBACK + ")"
        f, c = run_shape2(tmp, f"reloc_{label}", wat, [(s, ()) for s in seq], 0,
                          *tgt)
        fails += f
        compared += c
    print("=== shapes the decision cannot relocate (must be refused) ===")
    refusals = assert_refusals(tmp)
    # Non-vacuity for the refusal half (#1113): the emulation floor cannot
    # see a refused compile, so it is counted here.
    if refusals != len(REFUSE) + len(REFUSE_SP):
        print(f"VACUOUS: refusals={refusals} of {len(REFUSE) + len(REFUSE_SP)}")
        return 1
    print(f"refusals: {refusals}")
    print(f"\ncompared: {compared}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
