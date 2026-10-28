#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 58000
"""RQ-89-FLOATEXEC (#1609) — the spec suite's FLOAT assertions, EXECUTED on an
FPU target.

# The gap this closes

Until this oracle, NO spec-testsuite assertion that passes or returns an
f32/f64 was executed on any target. Both spec-execution oracles hard-code
`--target cortex-m4` (no FPU) and set float signatures aside:
`wast_conformance_928_differential.py` buckets them as `float-abi`, and
`selector_parity_197_differential.py` raises `Decl("float-abi")` on any
`f32.const`/`f64.const`. On cortex-m4 every function that touches a float is
declined with GI-FPU-002 before its float code is lowered, so the population
those two oracles execute contains no float lowering at all.

Two wrong-code defects shipped in this window that only execution sees —
#1594 (a float local's VFP home not zero-initialised; read-before-write saw a
temp's leftover or stack garbage) and #1603 (`i64.reinterpret_f64` returned
garbage). Both compiled with exit 0.

# What this does

For every `(module ...)` of the official spec suite (submodule) and
`tests/wast/`, on each FPU TARGET (`cortex-m7dp`: double-precision VFP;
`cortex-m4f`: single-precision VFP, so its f64 functions are declined by the
compiler and land in `symbol-missing`):

  1. COMPILE self-contained (`--all-exports --allow-skipped-exports`), the
     shipped default configuration, and ALSO on `cortex-m4` — the functions
     the FPU target compiles and cortex-m4 skips are the FPU-ONLY population:
     code no other spec-execution oracle has ever run.
  2. BOOT the image through its OWN shipped `Reset_Handler` under unicorn
     with the FPU enabled (CPACR CP10/CP11 full access, FPEXC.EN, FPSCR = 0:
     round-to-nearest, no flush-to-zero, no default-NaN), exactly as #197
     boots the cortex-m4 image — the R9/R10/R11 register contract and the
     data-segment copy are whatever synth emits, never re-stated here.
  3. EXECUTE every action of the file in order (state is shared, as in the
     spec), marshalling arguments by the AAPCS-VFP hard-float convention synth
     implements (`aapcs_param_layout` + `vfp_param_layout` in
     `synth-synthesis/src/instruction_selector.rs`): integer params take
     R0..R3 (i64 an even-aligned pair) SKIPPING float params; float params
     take the independent S0..S15 pool with BACK-FILL (an f64 takes the lowest
     free even S-pair as D(k), an f32 the lowest free S). Results are read
     from S0 (f32), D0 (f64), R0 (i32), R0:R1 (i64).
  4. EVERY assertion is executed in a GARBAGE machine state: random core
     registers R0..R12 (except the R9/R10/R11 contract and the argument
     registers), random S0..S31 (except argument registers), and a POISONED
     stack below the boot SP (0x41414141 / a quiet NaN / seeded random words)
     — the state that made #1594 visible. Every assertion that involves a
     float (float param/result, or a function only the FPU target compiles)
     is ALSO executed in a ZEROED state from the same memory snapshot; both
     runs must give the same, correct answer and the same linear memory.
     Callee-saved R4..R8 and S16..S31 (D8..D15) must survive the call, and
     R9/R10/R11/SP must equal their boot values — a violation is its own
     verdict, never hidden inside a value verdict.

# The expected value is the .wast literal, BIT-EXACT

The spec's own answer, not a second engine's opinion. A float literal is
turned into its bit pattern by wasmtime's own WAT parser (one
`i32.reinterpret_f32 (f32.const LIT)` probe function per distinct literal,
batched per file) — never by Python `float()`, which double-rounds f32
decimals (`const.wast`/`float_literals.wast` test exactly that). Results:

  bit-identical  the result's bits equal the literal's bits (a NaN LITERAL in
                 a result position — `f32.const nan:0x200000` — must match
                 bit-for-bit too: those are the sign/abs/neg/copysign tests);
  nan-class      the result matched a `nan:canonical` (payload exactly the
                 canonical one, either sign) or `nan:arithmetic` (quiet bit
                 set, either sign) PATTERN — counted separately, never folded
                 into bit-identical;
  MISMATCH       anything else, including a trap/fault/timeout where a value
                 was expected, and a missing trap where `assert_trap`
                 expected one (other than an out-of-bounds trap, which the
                 default envelope does not emit: `trap-envelope`, recorded).

wasmtime also runs every action in lock-step (the same declines, so the same
state). Where neither the arguments nor the literal are NaN and wasmtime disagrees
with the literal, the module state has fallen behind the script because of a
declined action. The image is then held to wasmtime's value, and the case is
counted as `reference-vs-literal`.

# Declines (counted and named, never silent)

  named-module, get-action, no-invoke, multi-value, either, ref-type, simd,
  stack-args (> 4 AAPCS core words), vfp-pool-overflow (> 16 S-slots),
  arity, symbol-missing (synth skipped the function — its #952 reason is
  tallied), symbol-unknown, exhaustion, f64-on-sp-target (an f64 signature
  reached a single-precision image), and module-level: imports,
  binary-module, module-decline (synth refused the module), boot-fault,
  wasmtime-instantiate.

# What GATES, and what is only recorded

GATED: every float-involved assertion, meaning one with a float param or result, or
one calling a function that only the FPU target compiles. Recorded but never gating:
  * integer assertions. They are executed, because module state is shared, but
    #197 owns them on cortex-m4. On these images they show the same envelope
    classes #197 pins: memory.grow fails in fixed SRAM (#539), #1206, and the
    OOB cascade.
  * a mismatch after an `assert_trap "out of bounds"` that the default image did
    not take. That is the no-bounds-check envelope's state cascade.
  * `reference-vs-literal`. An action declined on BOTH engines left the module
    state behind the script, and wasmtime disagrees with a non-NaN literal.
    The image is then held to wasmtime instead.

# Known MISMATCHES are PINNED, by exact count, with their issue

`KNOWN[(target, file, module ordinal, function, kind)] -> (issue, count)`.
RED when a pinned count MOVES in either direction or a pin VANISHES (the fix
landed: remove the pin in the same PR) and RED on any mismatch not pinned.

# Red-first (measured; transcript in artifacts/release-v0.89/RQ-89-FLOATEXEC.yaml)

A zero-mismatch run is not evidence on its own, so three controls:

  * A REAL shipped defect. On main 7e170d62, before PR #1607, the #1603 class
    shows up as 58 mismatches: conversions.wast `i64.reinterpret_f64` x15,
    endianness.wast `f64_load` x4 (its linear memory depends on the register
    garbage), and float_literals.wast x39. One of those, `i64.reinterpret_f64(+0.0)`,
    is wrong only in the GARBAGE state. On PR #1607's head binary exactly those
    three pins vanish and nothing else moves.
  * A PLANTED miscompile. Lowering `F32Add` as `F32Sub` in the shipped
    selector (`instruction_selector.rs`, the f32 binop arm) reds f32.wast
    `add` with 158 mismatches.
  * A NEW finding. #1614 (the f32 br-rendezvous slot overwrites the saved R4)
    was found by this oracle's callee-saved check on its first run.

Run (needs wasmtime + unicorn + pyelftools and the spec-testsuite submodule):
  SYNTH=./target/debug/synth python3 scripts/repro/spec_float_exec_1609_differential.py
  ... --only f32 --target cortex-m7dp     # a quick slice
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
import random
import re
import struct
import subprocess
import sys
import tempfile
import time
import zlib
from collections import Counter
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_HOOK_INTR, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as A

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SYNTH = os.environ.get("SYNTH", str(ROOT / "target" / "debug" / "synth"))
WAST_DIR = ROOT / "tests" / "wast"
SUITE_DIR = ROOT / "tests" / "spec-testsuite"

# The .wast reader is #197's — ONE parser for the spec corpus, not a mirror.
_spec = importlib.util.spec_from_file_location("sp197", HERE / "selector_parity_197_differential.py")
sp197 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sp197)
parse_sexp, modules_of, WastStr, Decl = sp197.parse_sexp, sp197.modules_of, sp197.WastStr, sp197.Decl
SKIP_RE = sp197.SKIP_RE

TARGETS = ("cortex-m7dp", "cortex-m4f")
DP_TARGETS = {"cortex-m7dp"}
M32 = 0xFFFFFFFF
M64 = (1 << 64) - 1
RET = 0x00F0_0000
INSN_LIMIT = 4_000_000
POISON_WINDOW = 0x2000
CORE_ARGS = [A.UC_ARM_REG_R0, A.UC_ARM_REG_R1, A.UC_ARM_REG_R2, A.UC_ARM_REG_R3]
SREG = [getattr(A, f"UC_ARM_REG_S{i}") for i in range(32)]
DREG = [getattr(A, f"UC_ARM_REG_D{i}") for i in range(16)]
CALLEE_SAVED_CORE = [getattr(A, f"UC_ARM_REG_R{i}") for i in range(4, 9)]
CONTRACT = [(A.UC_ARM_REG_R9, "R9"), (A.UC_ARM_REG_R10, "R10"), (A.UC_ARM_REG_R11, "R11")]

# ---------------------------------------------------------------------------
# FLOORS — non-vacuity, per full run (both targets, suite + tests/wast).
# Measured at authoring; see the RQ-89-FLOATEXEC record. Raise when the
# corpus grows, never lower to green a run.
# ---------------------------------------------------------------------------
# Measured on main 7e170d62 (spec-testsuite @ 3453673, wasmtime-py 48.0.0,
# both targets): float-signature actions executed 17,249; FPU-only-function
# actions 270; gated bit-identical 15,015; gated nan-class 2,228 (PR #1607's
# head: 17,262 / 286 / 15,102 / 2,228 — its fix lets 13 + 16 more compile).
FLOORS_FULL = dict(float_assertions=16_500, fpu_only_assertions=250, bit_identical=14_500, nan_class=2_100)
FLOORS_LOCAL = dict(float_assertions=1, fpu_only_assertions=0, bit_identical=1, nan_class=0)

# ---------------------------------------------------------------------------
# KNOWN mismatches — (target, file, module ordinal, function, kind) ->
# (issue, count). Exact counts: a pin that moves in EITHER direction is red.
# ---------------------------------------------------------------------------
KNOWN: dict[tuple[str, str, int, str, str], tuple[str, int]] = {
    # #1614 — an f32 carried over br/br_if/br_table to a block join is stored
    # to the #1318 rendezvous slot at [sp, #0] with NO frame reserved, i.e.
    # into the prologue's saved-R4 slot; the epilogue then hands the caller
    # back R4 = the float's bits. The VALUE is right (so the literal passes);
    # the AAPCS callee-saved contract is not. Both FPU targets, both images.
    ("cortex-m7dp", "br.wast", 0, "type-f32-value", "contract-violation"): ("#1614", 1),
    ("cortex-m7dp", "br.wast", 0, "as-unary-operand", "contract-violation"): ("#1614", 1),
    ("cortex-m7dp", "br_if.wast", 0, "type-f32-value", "contract-violation"): ("#1614", 1),
    ("cortex-m7dp", "br_table.wast", 0, "type-f32-value", "contract-violation"): ("#1614", 1),
    ("cortex-m7dp", "br_table.wast", 0, "as-unary-operand", "contract-violation"): ("#1614", 1),
    ("cortex-m4f", "br.wast", 0, "type-f32-value", "contract-violation"): ("#1614", 1),
    ("cortex-m4f", "br.wast", 0, "as-unary-operand", "contract-violation"): ("#1614", 1),
    ("cortex-m4f", "br_if.wast", 0, "type-f32-value", "contract-violation"): ("#1614", 1),
    ("cortex-m4f", "br_table.wast", 0, "type-f32-value", "contract-violation"): ("#1614", 1),
    ("cortex-m4f", "br_table.wast", 0, "as-unary-operand", "contract-violation"): ("#1614", 1),
    # #1603 — `i64.reinterpret_f64` returned garbage (the high/low words of
    # the D-register never reached R0:R1). Fixed by PR #1607 (RQ-89-REINTERP),
    # which had NOT merged when this table was measured on main 7e170d62.
    # Measured on PR #1607's head (85e984dc): EXACTLY these three pins vanish
    # and nothing else moves — so when #1607 lands this oracle goes red with
    # three VANISHED lines, and these three entries are deleted. float_literals
    # reads every f64 literal back through `i64.reinterpret_f64` (39 functions,
    # one class: the module wildcard); endianness's `f64_load` stores the
    # reinterpreted bits, so its linear memory depends on the register garbage.
    ("cortex-m7dp", "conversions.wast", 0, "i64.reinterpret_f64", "mismatch/value"): ("#1603", 15),
    ("cortex-m7dp", "endianness.wast", 0, "f64_load", "state-dependent-memory"): ("#1603", 4),
    ("cortex-m7dp", "float_literals.wast", 0, "*", "mismatch/value"): ("#1603", 39),
}



# ---------------------------------------------------------------------------
# Literals -> bits, by wasmtime's own WAT parser
# ---------------------------------------------------------------------------
NAN_PATTERNS = ("nan:canonical", "nan:arithmetic")


def collect_literals(form, out: set):
    if isinstance(form, list):
        if len(form) == 2 and form[0] in ("f32.const", "f64.const") and isinstance(form[1], str) \
                and form[1] not in NAN_PATTERNS:
            out.add((form[0][:3], form[1]))
        else:
            for f in form:
                collect_literals(f, out)


def literal_bits(engine, lits: set) -> dict:
    """{(ty, text): bits} — one probe function per literal, ONE module."""
    lits = sorted(lits)
    if not lits:
        return {}
    funcs = []
    for i, (ty, txt) in enumerate(lits):
        if ty == "f32":
            funcs.append(f'(func (export "k{i}") (result i32) (i32.reinterpret_f32 (f32.const {txt})))')
        else:
            funcs.append(f'(func (export "k{i}") (result i64) (i64.reinterpret_f64 (f64.const {txt})))')
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, wasmtime.Module(engine, "(module " + "\n".join(funcs) + ")"), [])
    ex = inst.exports(store)
    out = {}
    for i, key in enumerate(lits):
        v = ex[f"k{i}"](store)
        out[key] = v & (M32 if key[0] == "f32" else M64)
    return out


def value_of(form, bits: dict):
    """A const form -> (ty, value-or-pattern). Floats are BITS."""
    if not isinstance(form, list) or not form:
        raise Decl("non-const-arg")
    head = form[0]
    if head in ("i32.const", "i64.const"):
        return sp197.parse_const(form)
    if head in ("f32.const", "f64.const"):
        ty = head[:3]
        if form[1] in NAN_PATTERNS:
            return ty, form[1]
        return ty, bits[(ty, form[1])]
    if head == "either":
        raise Decl("either")
    if head.startswith("ref."):
        raise Decl("ref-type")
    if head == "v128.const":
        raise Decl("simd")
    raise Decl(f"unknown-const:{head}")


def is_nan(ty: str, b: int) -> bool:
    if ty == "f32":
        return (b & 0x7F800000) == 0x7F800000 and (b & 0x7FFFFF) != 0
    if ty == "f64":
        return (b & 0x7FF0000000000000) == 0x7FF0000000000000 and (b & 0xFFFFFFFFFFFFF) != 0
    return False


def nan_match(ty: str, pattern: str, b: int) -> bool:
    if ty == "f32":
        mag = b & 0x7FFFFFFF
        return mag == 0x7FC00000 if pattern == "nan:canonical" else (mag & 0x7FC00000) == 0x7FC00000
    mag = b & 0x7FFFFFFFFFFFFFFF
    q = 0x7FF8000000000000
    return mag == q if pattern == "nan:canonical" else (mag & q) == q


# ---------------------------------------------------------------------------
# AAPCS-VFP marshalling — synth's own convention (instruction_selector.rs)
# ---------------------------------------------------------------------------
def marshal(params: list[str], args: list[tuple[str, object]], dp: bool):
    """-> (core_words, [(sreg_index, bits32)])."""
    core: list[int] = []
    taken = [False] * 16
    sregs: list[tuple[int, int]] = []
    for ty, v in args:
        if ty == "f32":
            k = next((k for k in range(16) if not taken[k]), None)
            if k is None:
                raise Decl("vfp-pool-overflow")
            taken[k] = True
            sregs.append((k, v & M32))
        elif ty == "f64":
            if not dp:
                raise Decl("f64-on-sp-target")
            k = next((k for k in range(8) if not taken[2 * k] and not taken[2 * k + 1]), None)
            if k is None:
                raise Decl("vfp-pool-overflow")
            taken[2 * k] = taken[2 * k + 1] = True
            sregs += [(2 * k, v & M32), (2 * k + 1, (v >> 32) & M32)]
        elif ty == "i32":
            core.append(v & M32)
        else:  # i64
            if len(core) % 2:
                core.append(None)  # alignment hole: keeps its garbage
            core += [v & M32, (v >> 32) & M32]
    if len(core) > 4:
        raise Decl("stack-args")
    return core, sregs


# ---------------------------------------------------------------------------
# The image — booted through its own Reset_Handler, FPU enabled
# ---------------------------------------------------------------------------
class Image:
    def __init__(self, elf_path: Path):
        with elf_path.open("rb") as fh:
            elf = ELFFile(fh)
            st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
            self.syms = {s.name: s["st_value"] for s in st.iter_symbols() if s.name}
            segs = [(sg["p_vaddr"], sg["p_memsz"], sg.data())
                    for sg in elf.iter_segments() if sg["p_type"] == "PT_LOAD"]
        self.mu = mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.ctl_set_cpu_model(A.UC_CPU_ARM_MAX)
        text_va, _, text = min(segs, key=lambda s: s[0])
        sp0, reset = struct.unpack_from("<II", text, 0)
        self.sp0 = sp0
        ram = [(va, sz) for va, sz, _ in segs if va != text_va]
        ram_lo = min((va for va, _ in ram), default=sp0 - 0x20000) & ~0xFFF
        ram_hi = max(sp0, max((va + sz for va, sz in ram), default=0))
        ram_hi = (ram_hi + 0xFFF) & ~0xFFF
        self.ram = (ram_lo, ram_hi)
        mu.mem_map(text_va & ~0xFFF, ((text_va + len(text) + 0xFFF) & ~0xFFF) - (text_va & ~0xFFF))
        mu.mem_write(text_va, text)
        mu.mem_map(ram_lo, ram_hi - ram_lo)
        for va, _, data in segs:
            if va != text_va and data:
                mu.mem_write(va, data)
        mu.mem_map(RET & ~0xFFF, 0x1000)
        # The shipped FPU-target startup enables the FPU itself by a
        # read-modify-write of CPACR (0xE000ED88, SCB); map the SCB page so
        # that write lands. Unicorn's FPU gate is the coprocessor register
        # below, so both are set: synth's own startup runs unmodified.
        mu.mem_map(0xE000E000, 0x1000)
        # FPU on (CP10/CP11 full access, FPEXC.EN), FPSCR = 0 (RN, no FZ/DN).
        mu.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)
        mu.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)
        mu.reg_write(A.UC_ARM_REG_FPSCR, 0)
        mu.reg_write(A.UC_ARM_REG_SP, sp0)
        pc = reset & ~1
        while True:
            hw = struct.unpack_from("<H", text, pc - text_va)[0]
            if hw == 0x4780:  # blx r0 into the entry function
                break
            pc += 4 if (hw >> 11) in (0b11101, 0b11110, 0b11111) else 2
        mu.emu_start(reset | 1, pc, count=INSN_LIMIT)
        self.boot = {r: mu.reg_read(r) & M32 for r, _ in CONTRACT}
        self.mem_base = self.boot[A.UC_ARM_REG_R11]
        self.mem_size = self.boot[A.UC_ARM_REG_R10]
        # The poison window: below the boot SP, never overlapping a loaded
        # segment or linear memory (poisoning program state would be a false
        # alarm, not a finding).
        top_data = max([va + sz for va, sz in ram if va + sz <= sp0] +
                       ([self.mem_base + self.mem_size] if self.mem_base + self.mem_size <= sp0 else []) +
                       [ram_lo])
        self.poison = (max(top_data, sp0 - POISON_WINDOW), sp0)
        self.trapped = False
        trap = self.syms.get("Trap_Handler", 0) & ~1

        def on_trap(uc, addr, size, _):
            self.trapped = True
            uc.emu_stop()

        def on_intr(uc, intno, _):
            self.trapped = True
            uc.emu_stop()

        if trap:
            mu.hook_add(UC_HOOK_CODE, on_trap, begin=trap, end=trap + 1)
        mu.hook_add(UC_HOOK_INTR, on_intr)

    def snapshot(self) -> bytes:
        # Program state lives below the poison window (globals, linear
        # memory, data); the window itself is re-poisoned before every call.
        lo, hi = self.ram[0], self.poison[0]
        return bytes(self.mu.mem_read(lo, hi - lo))

    def restore(self, snap: bytes):
        self.mu.mem_write(self.ram[0], snap)

    def memory(self) -> bytes:
        if not self.mem_size:
            return b""
        return bytes(self.mu.mem_read(self.mem_base, self.mem_size))

    def call(self, fn, core, sregs, results, garbage: bool, rng: random.Random):
        """-> (('ok', value) | ('trap',) | ('fault', msg) | ('timeout',), [violations])"""
        mu = self.mu
        if garbage:
            lo, hi = self.poison
            pat = rng.randrange(3)
            if pat == 2:
                mu.mem_write(lo, rng.randbytes(hi - lo))
            else:
                mu.mem_write(lo, struct.pack("<I", (0x41414141, 0x7FC00001)[pat]) * ((hi - lo) // 4))
        for i, r in enumerate(SREG):
            mu.reg_write(r, rng.getrandbits(32) if garbage else 0)
        for i in range(13):
            r = getattr(A, f"UC_ARM_REG_R{i}")
            mu.reg_write(r, rng.getrandbits(32) if garbage else 0)
        for r, _ in CONTRACT:
            mu.reg_write(r, self.boot[r])
        for r, w in zip(CORE_ARGS, core):
            if w is not None:
                mu.reg_write(r, w)
        for k, w in sregs:
            mu.reg_write(SREG[k], w)
        mu.reg_write(A.UC_ARM_REG_FPSCR, 0)
        saved_core = {r: mu.reg_read(r) & M32 for r in CALLEE_SAVED_CORE}
        saved_vfp = {k: mu.reg_read(SREG[k]) & M32 for k in range(16, 32)}
        mu.reg_write(A.UC_ARM_REG_SP, self.sp0)
        mu.reg_write(A.UC_ARM_REG_LR, RET | 1)
        self.trapped = False
        try:
            mu.emu_start(self.syms[fn] | 1, RET, count=INSN_LIMIT)
        except UcError as e:
            return ("fault", str(e)), []
        if self.trapped:
            return ("trap",), []
        if (mu.reg_read(A.UC_ARM_REG_PC) & ~1) != RET:
            return ("timeout",), []
        viol = []
        for r, name in CONTRACT:
            got = mu.reg_read(r) & M32
            if got != self.boot[r]:
                viol.append(f"{name} clobbered")
        if (mu.reg_read(A.UC_ARM_REG_SP) & M32) != self.sp0:
            viol.append("SP imbalance")
        for r, w in saved_core.items():
            if (mu.reg_read(r) & M32) != w:
                viol.append(f"R{CALLEE_SAVED_CORE.index(r) + 4} not preserved")
        for k, w in saved_vfp.items():
            if (mu.reg_read(SREG[k]) & M32) != w:
                viol.append(f"S{k} not preserved")
        if not results:
            return ("ok", None), viol
        ty = results[0]
        if ty == "f32":
            v = mu.reg_read(SREG[0]) & M32
        elif ty == "f64":
            v = mu.reg_read(DREG[0]) & M64
        elif ty == "i32":
            v = mu.reg_read(A.UC_ARM_REG_R0) & M32
        else:
            v = (mu.reg_read(A.UC_ARM_REG_R0) & M32) | ((mu.reg_read(A.UC_ARM_REG_R1) & M32) << 32)
        return ("ok", v), viol


# ---------------------------------------------------------------------------
# wasmtime — the cross-check of THIS harness (never the expected value)
# ---------------------------------------------------------------------------
def to_py(ty: str, v: int):
    if ty == "i32":
        return v - (1 << 32) if v >> 31 else v
    if ty == "i64":
        return v - (1 << 64) if v >> 63 else v
    if ty == "f32":
        return struct.unpack("<f", struct.pack("<I", v))[0]
    return struct.unpack("<d", struct.pack("<Q", v))[0]


def from_py(ty: str, v) -> int:
    if ty == "i32":
        return v & M32
    if ty == "i64":
        return v & M64
    if ty == "f32":
        return struct.unpack("<I", struct.pack("<f", v))[0]
    return struct.unpack("<Q", struct.pack("<d", v))[0]


# ---------------------------------------------------------------------------
# Compilation
# ---------------------------------------------------------------------------
def compile_image(src: Path, out: Path, target: str):
    r = subprocess.run([SYNTH, "compile", str(src), "--target", target, "--all-exports",
                        "--allow-skipped-exports", "-o", str(out)],
                       capture_output=True, text=True, timeout=300)
    err = r.stdout + r.stderr
    skipped = {m.group(1): m.group(2).strip()[:160] for m in SKIP_RE.finditer(err)}
    if "panicked" in err:
        return None, skipped, "PANIC: " + err[-300:]
    if r.returncode != 0 or not out.exists():
        msg = next((l for l in err.splitlines() if l.startswith("Error")), err[-200:])
        return None, skipped, msg.strip()[:240]
    with out.open("rb") as fh:
        st = next(s for s in ELFFile(fh).iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        funcs = {s.name for s in st.iter_symbols() if s.name and s["st_info"]["type"] == "STT_FUNC"}
    return funcs - {"Reset_Handler", "Default_Handler", "Trap_Handler"}, skipped, ""


class Run:
    def __init__(self, target: str, file: str, idx: int):
        self.target, self.file, self.idx = target, file, idx
        self.decline = ""
        self.c: Counter = Counter()        # verdict counters
        self.declined: Counter = Counter()
        self.skip_reasons: Counter = Counter()
        self.mismatches: list[dict] = []   # GATED: pinned or red
        self.info: list[dict] = []         # recorded, never gating
        self.after_trap_miss = False
        self.emulations = 0
        self.seconds = 0.0


def classify(ty, expect, got):
    """-> 'bit-identical' | 'nan-class' | None (mismatch)."""
    if got[0] != "ok":
        return None
    if expect is None:
        return "bit-identical" if got[1] is None else None
    ety, ev = expect
    if isinstance(ev, str):
        return "nan-class" if nan_match(ety, ev, got[1]) else None
    mask = M32 if ety in ("i32", "f32") else M64
    return "bit-identical" if got[1] == (ev & mask) else None


def fmt(got):
    if got[0] == "ok":
        return "ok:" + ("-" if got[1] is None else f"0x{got[1]:x}")
    return ":".join(str(x) for x in got)


def run_module(engine, target: str, file: str, idx: int, wat: str, actions: list,
               bits: dict, m4_funcs, tmp: Path) -> Run:
    run = Run(target, file, idx)
    dp = target in DP_TARGETS
    sexp = parse_sexp(wat)
    if len(sexp) > 1 and isinstance(sexp[1], str) and sexp[1] in ("binary", "quote", "definition", "instance"):
        run.decline = "binary-module"
        return run
    kinds = [f[0] for f in sexp[1:] if isinstance(f, list) and f]
    if "import" in kinds:
        run.decline = "imports"
        return run
    src = tmp / f"m{idx}.wat"
    src.write_text(wat)
    out = tmp / f"m{idx}_{target}.elf"
    funcs, skipped, err = compile_image(src, out, target)
    run.skip_reasons.update(re.sub(r"\d+", "N", v)[:90] for v in skipped.values())
    if funcs is None:
        run.decline = "module-decline:" + err[:120]
        return run
    try:
        ref_mod = wasmtime.Module(engine, wat)
        store = wasmtime.Store(engine)
        ref = wasmtime.Instance(store, ref_mod, [])
        rex = ref.exports(store)
    except Exception as e:
        run.decline = "wasmtime-instantiate:" + str(e).splitlines()[0][:100]
        return run
    try:
        img = Image(out)
        run.emulations += 1
    except UcError as e:
        run.decline = f"boot-fault:{e}"
        return run
    rng = random.Random(zlib.crc32(f"{target}|{file}|{idx}".encode()))
    for act in actions:
        kind = act[0]
        if kind == "assert_exhaustion":
            run.declined["exhaustion"] += 1
            continue
        try:
            action = act if kind == "invoke" else (act[1] if len(act) > 1 else None)
            if not isinstance(action, list) or action[0] != "invoke":
                raise Decl("get-action" if isinstance(action, list) and action[0] == "get" else "no-invoke")
            if isinstance(action[1], str) and action[1].startswith("$"):
                raise Decl("named-module")
            fn = action[1].text()
            args = [value_of(a, bits) for a in action[2:]]
            expect = None
            if kind == "assert_return":
                exp = [value_of(e, bits) for e in act[2:]]
                if len(exp) > 1:
                    raise Decl("multi-value")
                expect = exp[0] if exp else None
            f = rex[fn] if fn in rex else None
            if not isinstance(f, wasmtime.Func):
                raise Decl("symbol-unknown")
            ft = f.type(store)
            params, results = [str(t) for t in ft.params], [str(t) for t in ft.results]
            if any(t not in ("i32", "i64", "f32", "f64") for t in params + results):
                raise Decl("ref-type")
            if len(results) > 1:
                raise Decl("multi-value")
            if len(params) != len(args) or [t for t, _ in args] != params:
                raise Decl("arity")
            if not dp and "f64" in results:
                raise Decl("f64-on-sp-target")
            if fn not in funcs:
                raise Decl("symbol-missing")
            core, sregs = marshal(params, args, dp)
        except Decl as e:
            run.declined[e.reason] += 1
            continue
        involves_float = any(t in ("f32", "f64") for t in params + results)
        fpu_only = m4_funcs is not None and fn not in m4_funcs
        floaty = involves_float or fpu_only
        # Reference (cross-check of this harness).
        has_nan = any(t in ("f32", "f64") and is_nan(t, v) for t, v in args)
        try:
            r = f(store, *[to_py(t, v) for t, v in args])
            wref = ("ok", None if r is None else from_py(results[0], r))
        except wasmtime.Trap:
            wref = ("trap",)
        # The image: zeroed state first (float-involved only), from a memory
        # snapshot, then the garbage state from the SAME snapshot.
        outs = {}
        snap = img.snapshot() if floaty else None
        mem_after = {}
        if floaty:
            res, viol = img.call(fn, core, sregs, results, False, rng)
            run.emulations += 1
            outs["zeroed"] = (res, viol)
            mem_after["zeroed"] = img.memory()
            img.restore(snap)
        res, viol = img.call(fn, core, sregs, results, True, rng)
        run.emulations += 1
        outs["garbage"] = (res, viol)
        mem_after["garbage"] = img.memory()
        detail = (f"{target} {file} m{idx} {fn}({','.join(f'{t}:0x{v:x}' for t, v in args)})")
        pop = "float" if involves_float else ("fpu-only" if fpu_only else "integer")
        run.c[f"executed/{pop}"] += 1
        if kind == "invoke":
            run.c["invoke"] += 1
            continue
        # GATED population: float-involved assertions (float signature, or a
        # function only the FPU target compiles). Integer assertions are
        # executed (state is shared) and recorded, but #197 owns them on
        # cortex-m4; a mismatch after an out-of-bounds trap the default image
        # does not emit is the envelope's state cascade (#197's
        # `shared-wrong-after-trap-miss`). Neither gates.
        gated = floaty and not run.after_trap_miss
        tag = pop if not floaty else "after-trap-miss"

        def record(kind_, text):
            if gated:
                run.c["MISMATCH"] += 1
                run.mismatches.append(dict(func=fn, kind=kind_, detail=text))
            else:
                run.c[f"informational/{tag}"] += 1
                run.info.append(dict(func=fn, kind=kind_, detail=text))

        if kind == "assert_trap":
            msg = act[-1].text() if isinstance(act[-1], WastStr) else ""
            if wref[0] != "trap":
                run.c["reference-no-trap"] += 1
                continue
            if all(o[0][0] in ("trap", "fault") for o in outs.values()):
                run.c["trap-ok"] += 1
                if gated:
                    run.c["gated"] += 1
                continue
            if "out of bounds" in msg:
                run.c["trap-envelope"] += 1
                run.after_trap_miss = True
                continue
            if gated:
                run.c["gated"] += 1
            record("trap-miss", detail + f" expected trap '{msg}', got " +
                   " ".join(f"{k}={fmt(o[0])}" for k, o in outs.items()))
            continue
        # The literal is the spec's answer for the spec's action sequence. An
        # action this harness declined (on BOTH engines, lock-step) can leave
        # the module state behind that sequence; wasmtime then disagrees with
        # the literal on a NON-NaN value. The image is then held to wasmtime
        # (same state as the image) — counted, never silent.
        if wref[0] == "ok" and expect is not None and not isinstance(expect[1], str) \
                and not has_nan and not is_nan(expect[0], expect[1]) \
                and wref[1] is not None and not is_nan(expect[0], wref[1]) \
                and wref[1] != (expect[1] & (M32 if expect[0] in ("i32", "f32") else M64)):
            run.c["reference-vs-literal"] += 1
            expect = (expect[0], wref[1])
        verdicts = {k: classify(results[0] if results else None, expect, o[0]) for k, o in outs.items()}
        viols = sorted({v for o in outs.values() for v in o[1]})
        if gated:
            run.c["gated"] += 1
        if viols:
            record("contract-violation", detail + " " + "; ".join(viols))
            continue
        if len(set(mem_after.values())) > 1:
            record("state-dependent-memory", detail)
            continue
        if all(v is not None for v in verdicts.values()):
            v = "nan-class" if "nan-class" in verdicts.values() else "bit-identical"
            run.c[v] += 1
            run.c[f"{v}/{pop}"] += 1
            continue
        bad = [k for k, v in verdicts.items() if v is None]
        sub = "value" if all(outs[k][0][0] == "ok" for k in bad) else "no-value"
        # Which machine state(s) disagreed goes in the DETAIL, never the pin
        # key: a pin must not move because garbage happened to equal zero.
        states = "+".join(bad)
        want = "-" if expect is None else (expect[1] if isinstance(expect[1], str) else f"0x{expect[1]:x}")
        record(f"mismatch/{sub}", detail + f" [{states}] want {want} got " +
               " ".join(f"{k}={fmt(o[0])}" for k, o in outs.items()))
    return run


def process_file(engine, wast: Path, targets, jobs_tmp: Path) -> list[Run]:
    t0 = time.monotonic()
    runs = _process_file(engine, wast, targets, jobs_tmp)
    for r in runs[:1]:
        r.seconds = time.monotonic() - t0
    return runs


def _process_file(engine, wast: Path, targets, jobs_tmp: Path) -> list[Run]:
    text = wast.read_text(errors="replace")
    runs = []
    mods = list(modules_of(text))
    lits: set = set()
    for _, _, actions in mods:
        for a in actions:
            collect_literals(a, lits)
    with tempfile.TemporaryDirectory(dir=jobs_tmp) as td:
        tdp = Path(td)
        try:
            bits = literal_bits(engine, lits)
        except Exception as e:
            r = Run("*", wast.name, -1)
            r.decline = f"harness-error:literals:{str(e)[:120]}"
            return [r]
        for idx, mod_text, actions in mods:
            if not actions:
                continue
            m4_funcs = None
            src = tdp / f"m{idx}.wat"
            src.write_text(mod_text)
            try:
                m4_funcs, _, _ = compile_image(src, tdp / f"m{idx}_m4.elf", "cortex-m4")
            except Exception:
                m4_funcs = None
            if m4_funcs is None:
                m4_funcs = set()
            for target in targets:
                try:
                    runs.append(run_module(engine, target, wast.name, idx, mod_text, actions,
                                           bits, m4_funcs, tdp))
                except Exception as e:
                    r = Run(target, wast.name, idx)
                    r.decline = f"harness-error:{type(e).__name__}:{str(e)[:120]}"
                    runs.append(r)
    return runs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-suite", action="store_true", help="tests/wast only (LOCAL floors)")
    ap.add_argument("--only", help="substring filter on file name")
    ap.add_argument("--target", action="append", choices=TARGETS)
    # Default ONE worker, measured: unicorn under Python threads is SLOWER,
    # not faster (tests/wast: -j1 4.7 s wall vs -j4 8.4 s, the difference all
    # system time; the full corpus 245 s at -j1 vs 965 s at -j8). Processes
    # would not help either: `oracle_run.py` counts emulator entries
    # IN-PROCESS, so work done in a child would vanish from the floor.
    ap.add_argument("-j", "--jobs", type=int, default=1)
    ap.add_argument("--json", help="write the full ledger here")
    ap.add_argument("--table", action="store_true", help="print the per-file result table")
    ap.add_argument("--wast", action="append", default=[],
                    help="run ONLY these .wast files (minimisation; LOCAL floors)")
    args = ap.parse_args()
    targets = tuple(args.target or TARGETS)

    files = sorted(WAST_DIR.glob("*.wast"))
    if not args.no_suite:
        suite = sorted(SUITE_DIR.glob("*.wast"))
        if not suite:
            print(f"FAIL: {SUITE_DIR} is empty — needs `submodules: recursive` (or --no-suite).")
            return 1
        files += suite
    if args.wast:
        files = [Path(w).resolve() for w in args.wast]
    if args.only:
        files = [f for f in files if args.only in f.name]
    if not files:
        print("FAIL: no corpus files")
        return 1
    if not Path(SYNTH).is_file():
        print(f"FAIL: synth not found at {SYNTH}")
        return 1

    engine = wasmtime.Engine()
    runs: list[Run] = []
    with tempfile.TemporaryDirectory() as td, \
            concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for rs in ex.map(lambda f: process_file(engine, f, targets, Path(td)), files):
            runs.extend(rs)

    tot, declined, mdecl, skips = Counter(), Counter(), Counter(), Counter()
    per_file: dict = {}
    actual: Counter = Counter()
    lines, info_lines = [], []
    for r in runs:
        tot.update(r.c)
        declined.update(r.declined)
        skips.update(r.skip_reasons)
        if r.decline:
            mdecl[r.decline.split(":")[0]] += 1
        pf = per_file.setdefault((r.target, r.file), Counter())
        pf.update(r.c)
        pf["skipped"] += sum(r.declined.values())
        if r.decline:
            pf["module-declined"] += 1
        for m in r.mismatches:
            lines.append(f"{m['kind']}: {m['detail']}")
            actual[(r.target, r.file, r.idx, m["func"], m["kind"])] += 1
        info_lines.extend(f"{m['kind']}: {m['detail']}" for m in r.info)
    executed = sum(v for k, v in tot.items() if k.startswith("executed/"))
    float_asserts = tot["executed/float"]
    fpu_only = tot["executed/fpu-only"]

    print(f"#1609 spec float execution — targets {','.join(targets)}, {len(files)} files, "
          f"{len(runs)} (target, module) runs")
    print(f"  module-level declines: " + (", ".join(f"{k}={v}" for k, v in sorted(mdecl.items())) or "none"))
    print(f"  actions executed: {executed}  (float signature: {float_asserts}, FPU-only function: "
          f"{fpu_only}, integer: {tot['executed/integer']}; plain invokes: {tot['invoke']})")
    fl_bits = tot["bit-identical/float"] + tot["bit-identical/fpu-only"]
    fl_nan = tot["nan-class/float"] + tot["nan-class/fpu-only"]
    print(f"  GATED (float-involved) assertions: {tot['gated']} — bit-identical={fl_bits} "
          f"nan-class={fl_nan} trap-ok(gated)={tot['gated'] - fl_bits - fl_nan - tot['MISMATCH']} "
          f"MISMATCH={tot['MISMATCH']}")
    print(f"  all populations: bit-identical={tot['bit-identical']} nan-class={tot['nan-class']} "
          f"trap-ok={tot['trap-ok']} trap-envelope={tot['trap-envelope']} "
          f"reference-vs-literal={tot['reference-vs-literal']} reference-no-trap={tot['reference-no-trap']}")
    print(f"  informational (never gating): " + (", ".join(
        f"{k.split('/', 1)[1]}={v}" for k, v in sorted(tot.items()) if k.startswith("informational/")) or "none"))
    print(f"  skipped by reason: " + (", ".join(f"{k}={v}" for k, v in sorted(declined.items())) or "none"))
    print(f"  synth skip reasons (top): " + "; ".join(f"{v}x {k}" for k, v in skips.most_common(6)))
    if args.table:
        print(f"  {'target':12s} {'file':34s} {'float':>6s} {'bits':>6s} {'nan':>5s} {'trap':>5s} "
              f"{'MISM':>5s} {'skip':>6s} {'mdecl':>5s} {'int':>6s}")
        for (t, f), c in sorted(per_file.items()):
            if not c["gated"]:
                continue
            fb = c["bit-identical/float"] + c["bit-identical/fpu-only"]
            fn_ = c["nan-class/float"] + c["nan-class/fpu-only"]
            print(f"  {t:12s} {f:34s} {c['gated']:6d} {fb:6d} {fn_:5d} "
                  f"{c['gated'] - fb - fn_ - c['MISMATCH']:5d} {c['MISMATCH']:5d} {c['skipped']:6d} "
                  f"{c['module-declined']:5d} {c['executed/integer']:6d}")
    slow = sorted(((r.seconds, r.file) for r in runs if r.seconds), reverse=True)[:5]
    print("  slowest files: " + ", ".join(f"{f} {s:.0f}s" for s, f in slow))
    print(f"  mismatches: {len(lines)}")
    for line in lines[:80]:
        print(f"    {line}")
    if len(lines) > 80:
        print(f"    ... and {len(lines) - 80} more (see --json)")

    if args.json:
        Path(args.json).write_text(json.dumps(dict(
            totals=tot, declined=declined, module_declines=mdecl, skip_reasons=skips,
            per_file={f"{t} {f}": c for (t, f), c in per_file.items()},
            mismatches=lines, informational=info_lines,
            pins={"|".join(map(str, k)): v for k, v in actual.items()},
            runs=[dict(target=r.target, file=r.file, idx=r.idx, decline=r.decline, c=r.c,
                       declined=r.declined, mismatches=r.mismatches, info=r.info) for r in runs],
        ), indent=1, default=str))

    fails = []
    floors = FLOORS_LOCAL if (args.no_suite or args.only or args.target or args.wast) else FLOORS_FULL
    measured = dict(float_assertions=float_asserts, fpu_only_assertions=fpu_only,
                    bit_identical=tot["bit-identical/float"] + tot["bit-identical/fpu-only"],
                    nan_class=tot["nan-class/float"] + tot["nan-class/fpu-only"])
    for k, floor in floors.items():
        if measured[k] < floor:
            fails.append(f"NON-VACUITY: {k} = {measured[k]} < floor {floor}")
    ran = {(t, f.name) for t in targets for f in files}
    # A pin whose function is "*" covers a whole module (one class hitting
    # every function of a spec module) — still an exact count, over the
    # module. Same convention as #197's KNOWN.
    wild = {k for k in KNOWN if k[3] == "*"}
    folded: Counter = Counter()
    for (t, f, i, fn, kind), n in actual.items():
        wk = (t, f, i, "*", kind)
        folded[wk if wk in wild else (t, f, i, fn, kind)] += n
    actual = folded
    pinned_ok = unpinned = 0
    for key, n in sorted(actual.items()):
        if key in KNOWN and KNOWN[key][1] == n:
            pinned_ok += n
            continue
        unpinned += n
        if key in KNOWN:
            fails.append(f"PINNED MISMATCH MOVED: {key}: {n} != pinned {KNOWN[key][1]} ({KNOWN[key][0]})")
        else:
            fails.append(f"NEW MISMATCH (not pinned): {key} x{n}")
    for key, (issue, n) in KNOWN.items():
        if (key[0], key[1]) in ran and key not in actual:
            fails.append(f"PINNED MISMATCH VANISHED: {key} (pinned {n}, {issue}) — the fix landed? "
                         f"remove the pin in the same PR")
    herr = [f"{r.target} {r.file} m{r.idx}: {r.decline}" for r in runs if r.decline.startswith("harness-error")]
    if herr:
        fails.append(f"HARNESS ERROR on {len(herr)} run(s): " + "; ".join(herr[:5]))
    gated = tot["gated"]
    print(f"  pinned known mismatches: {pinned_ok}; unpinned: {unpinned}")
    print(f"#1609 CHECKS={gated - unpinned}/{gated} assertions on FPU targets "
          f"({float_asserts + fpu_only} float-involved)")
    if fails:
        for f in fails[:60]:
            print(f"FAIL: {f}")
        if len(fails) > 60:
            print(f"FAIL: ... and {len(fails) - 60} more")
        return 1
    print("RESULT: PASS — every executed assertion on the FPU targets matches the .wast literal "
          "bit-exactly (or its NaN class), or is a pinned known mismatch")
    return 0


if __name__ == "__main__":
    sys.exit(main())
