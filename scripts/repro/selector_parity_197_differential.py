#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 20000
"""RQ-65-PARITY (#197) — the two SHIPPED lowering paths, differentially compared.

# The two engines

synth's ARM backend has TWO independent lowering paths over the same WASM
semantics, and both ship:

  * the OPTIMIZED path — `OptimizerBridge::optimize_full` -> `ir_to_arm`
    (`synth-synthesis/src/optimizer_bridge.rs`): the default for a
    self-contained image, per function, unless a routing predicate in
    `arm_backend.rs` diverts it (br_table, value-carrying branches, i64/float
    signatures, wide globals, read-before-write locals, fact-spec marks) or
    `ir_to_arm` returns Err and it falls back;
  * the DIRECT path — `select_with_stack`
    (`synth-synthesis/src/instruction_selector/select_with_stack.rs`): forced
    for `--relocatable` (#197), `--no-optimize`, and every diverted function.
    (`select_default` is NOT a third shipped path: it is this selector's
    `_ =>` fallthrough for ops its own match does not cover, and is reachable
    in full only through the test-only `select()` API — its own module header
    says so.)

Until this oracle they had never been compared. The same module compiled twice
— default flags vs `--no-optimize`, otherwise identical — must produce images
that BEHAVE identically; and both must agree with wasmtime. That is the North
Star's first invariant ("derive what you check against from the artifact you
ship") pointed at a second engine synth already builds and maintains.

# What is compared

For every `(module ...)` in the corpus (tests/wast/ plus the official spec
test suite submodule when present):

  1. COMPILE both legs (`--target cortex-m4 --all-exports
     --allow-skipped-exports`, +`--no-optimize` for the direct leg) and record
     the per-leg, per-function outcome. A function one leg compiles and the
     other declines is a RECORDED DIVERGENCE with the machine reason synth
     printed — never a failure. The optimized leg additionally reports, via
     `SYNTH_PATH_DEBUG`, which path each function actually took and WHY
     (`reasons=br-table,...` / `fallback: ...`), so a "both accepted" module
     can be told apart from "both accepted, and both were really the direct
     selector" — the parity population is the functions whose BYTES differ.
  2. EXECUTE the file's assertions, in file order, against THREE engines
     kept in lock-step: wasmtime (reference), the optimized image, the direct
     image. Each image boots through its OWN shipped `Reset_Handler` under
     unicorn, so the register contract (R9 globals / R10 size / R11 base) and
     the #758 data-segment copy are whatever synth actually emits — never a
     harness-side re-statement of the contract (the #377/#1021 harnesses seed
     R11 themselves and could not have seen the finding below).
  3. COMPARE per assertion: return value(s) or trap, R9/R10/R11 and SP
     preservation across the call, and the linear-memory image
     (`[R11, R11+R10)`) leg-vs-leg — and vs wasmtime whenever the module
     exports its memory.

# Verdict categories (every executed assertion lands in exactly one)

  ok                 all three agree
  parity-divergence  optimized != direct  (sub-classified opt-wrong /
                     direct-wrong / both-wrong-differently vs wasmtime)  FAIL
  shared-wrong       optimized == direct != wasmtime — invisible to parity by
                     construction, visible only because wasmtime is the third
                     engine                                                FAIL
  shared-wrong-after-trap-miss  same shape, but AFTER an `assert_trap` both
                     legs did not honour (the compliance envelope: default
                     images emit no OOB trap) — state has legitimately
                     diverged from wasmtime, so recorded, not failed
  trap-miss          assert_trap where wasmtime trapped and neither leg did,
                     both legs agreeing — the envelope, recorded

# Declines (counted and named, never silent)

  float-abi, ref-type, multi-value, arity, stack-args (> 4 AAPCS words),
  imports, named-module, binary-module, start-function (#1046),
  symbol-missing (one leg declined the function — the divergence record),
  symbol-unknown, wasmtime-instantiate:<err>, exhaustion (assert_exhaustion
  is never run), reference-vs-literal (wasmtime disagrees with the .wast
  literal — a fixture written for fresh-instance semantics; informational),
  trap-parity-envelope (the legs disagree on HOW an out-of-bounds access
  misbehaves — undefined under the default no-bounds-check envelope).
  A declined action is skipped on ALL three engines, so they stay in
  lock-step with each other and no later comparison is lost.

# Non-vacuity, ratcheted

A parity oracle that compares nothing must be RED. Four floors, each on a
number that means something: modules both legs accepted, assertions compared,
functions the OPTIMIZED path actually produced (else "both legs" is the direct
selector twice), and functions whose bytes DIFFER between the legs (the real
differential population). Plus the driver-level `ci-checks: emulations` floor
on emulator entries. Raise them when the corpus grows; a drop is a module that
stopped compiling or an op that started declining — a regression to explain.

# Known divergences are PINNED, by exact count, with their issue

The first run found four defects in the default self-contained configuration
on tests/wast alone (#1203 fixed alongside this oracle; #1204/#1205/#1206
open) and seven more on the spec suite — the first time the suite was ever
EXECUTED against synth rather than compiled (#1208 optimized narrow i64
loads lower to an empty body; #1209 memory64 accepted and silently wrong;
#1210 a value live across a call inside a value-carrying block is lost on
BOTH selectors; #1211 call_indirect ignores the table index; #1213 i64
select + wrap on the optimized path; #1214 i64 read-before-write local not
zero-initialised; #1215 branch-in-operand br_table/br_if shapes).
RQ-65-DECLINE (v0.65) then CONVERTED the three optimized-path-only classes
whose shapes the direct selector already lowers correctly — #1208 (nine
narrow i64 memory forms), #1213 (i64 select), #1205 (value-`if` with a
computed condition) — into declines with a machine reason, so their pins
below moved to `ok` and were removed; #1204/#1206 stay pinned (not
decline-shaped: a register-contract fix and a class without a statable
predicate), and the both-selectors-wrong classes stay pinned. An open finding
is pinned in KNOWN below as (file, module, function, kind) -> (issue, count):
the oracle is RED when a pinned count MOVES in either direction — the fix
landed (move the pin, close the issue on the release) or a new instance
appeared — and RED on any divergence that is not pinned. A pin is never a
waiver: it is the red-first witness kept red on purpose (the #1189 shape).

# Red-first

No harness-side plant: a knob that makes the harness disagree with itself
tests the knob. The transcript in the RQ-65-PARITY PR mutates ONE selector
arm (a `select_with_stack` lowering) and shows this oracle naming the module,
the function and the two disagreeing values, then restores it.

Run (needs wasmtime + unicorn + pyelftools; submodule optional locally):
  SYNTH=./target/debug/synth python3 scripts/repro/selector_parity_197_differential.py
  python3 scripts/repro/selector_parity_197_differential.py --no-suite   # tests/wast + own fixtures
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_HOOK_INTR, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

ROOT = Path(__file__).resolve().parent.parent.parent
SYNTH = os.environ.get("SYNTH", str(ROOT / "target" / "debug" / "synth"))
WAST_DIR = ROOT / "tests" / "wast"
SUITE_DIR = ROOT / "tests" / "spec-testsuite"
# This oracle's own witnesses (the two mixed-image shapes the first run found;
# see the module docstring). Same .wast grammar, executed with the corpus.
OWN_FIXTURES = sorted((ROOT / "scripts" / "repro").glob("selector_parity_197_*.wast"))

M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF
RET = 0x00F0_0000  # return sentinel: LR points here, emu_start stops here
INSN_LIMIT = 4_000_000
ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

LEGS = (("optimized", []), ("direct", ["--no-optimize"]))

# ---------------------------------------------------------------------------
# FLOORS — non-vacuity. See the module docstring. Measured on the corpus at
# authoring (tests/wast + own fixtures + spec-testsuite @ the pinned submodule
# commit 3453673): modules both legs accepted 326 (164 mixed-path),
# assertions executed on all three engines 19,145 under wasmtime-py 48.0.0
# (the CI-pinned reference engine; 46 cannot parse the suite's br_table.wast),
# optimized-path functions 1,267, byte-differing functions 1,479 (of 2,391
# common), emulator entries 27,362. Floors sit a few percent under the measurement; raise them when the
# corpus grows, never lower them to green a run.
# `--no-suite` (tests/wast + own fixtures) applies the smaller LOCAL floors so
# a submodule-less checkout still runs and still cannot compare nothing.
# ---------------------------------------------------------------------------
FLOORS_FULL = dict(modules_both=300, assertions_compared=14_500,
                   optimized_funcs=1_150, differing_funcs=1_350)
FLOORS_LOCAL = dict(modules_both=20, assertions_compared=200,
                    optimized_funcs=30, differing_funcs=20)
# RQ-65-MVPCORE (#1017): start-function modules that must be both-accepted
# and BOOTED whenever start.wast is in the run (full and `--only start`
# alike). Measured at authoring on the compiler that invokes the start
# function from Reset_Handler; 0 on the compiler before it (every start
# module refused, #1046).
START_MODULES_FLOOR = 1

# ---------------------------------------------------------------------------
# KNOWN divergences — (file, module ordinal, function, kind) -> (issue, count).
# Exact counts: a pin that moves in EITHER direction is red. See docstring.
# ---------------------------------------------------------------------------
KNOWN: dict[tuple[str, int, str, str], tuple[str, int]] = {
    # #1204 — optimized path leaves R11 = 0/1 on return (callee-saved; the direct
    # selector's memory base). Value right, the next direct-routed caller wrong —
    # executed by the r11_clobber fixture's `caller`.
    ('control_nested_select.wast', 0, 'nested_const_conds', 'contract-violation/optimized'): ('#1204', 4),
    ('control_nested_select.wast', 0, 'nested_if_else', 'contract-violation/optimized'): ('#1204', 4),
    ('int_literals.wast', 0, 'i64.inc_smin', 'contract-violation/optimized'): ('#1204', 1),
    ('selector_parity_197_r11_clobber.wast', 0, 'caller', 'contract-violation/optimized'): ('#1204', 3),
    ('selector_parity_197_r11_clobber.wast', 0, 'caller', 'parity-divergence/opt-wrong'): ('#1204', 1),
    ('selector_parity_197_r11_clobber.wast', 0, 'leaf', 'contract-violation/optimized'): ('#1204', 2),
    # #1205 — optimized path: value-`if` with simple arms and a COMPUTED
    # condition compared the constants and selected between the condition's
    # operands. CONVERTED to a decline in v0.65 (RQ-65-DECLINE): the shape
    # falls back to the direct selector, its 9 pinned wrong answers are `ok`.
    # #1206 — optimized path: loop label placed after the decrement of a
    # pre-loop-defined local; countdown(5)/(10) never terminate.
    ('control_loop.wast', 0, 'countdown', 'parity-divergence/opt-wrong'): ('#1206', 2),
    # #1208 — optimized path lowered i64.load8/16/32_{s,u} to an EMPTY body
    # (bx lr) and i64.store8/16/32 to a dropped store. CONVERTED to a decline
    # in v0.65 (RQ-65-DECLINE, the #372 guard extended to the nine narrow
    # forms): address.wast m1's 90 pinned wrong answers are `ok`.
    # #1213 — optimized path: i64 select (register-pair operands). CONVERTED
    # to a decline in v0.65 (RQ-65-DECLINE): select.wast as-convert-operand
    # is `ok`.
    # #1209 — memory64 modules accepted and silently wrong on both selectors
    # (i64-offset data segments dropped; optimized mis-addresses i64 addresses).
    # Whole-module pins per kind: one class hits every function.
    ('address64.wast', 0, '*', 'shared-wrong'): ('#1209', 25),
    ('address64.wast', 1, '*', 'shared-wrong'): ('#1209', 35),
    ('float_memory64.wast', 0, '*', 'shared-wrong'): ('#1209', 1),
    ('float_memory64.wast', 1, '*', 'shared-wrong'): ('#1209', 1),
    ('float_memory64.wast', 2, '*', 'parity-divergence/memory-only'): ('#1209', 2),
    ('float_memory64.wast', 2, '*', 'shared-wrong'): ('#1209', 1),
    ('float_memory64.wast', 3, '*', 'shared-wrong'): ('#1209', 1),
    ('float_memory64.wast', 4, '*', 'shared-wrong'): ('#1209', 1),
    ('float_memory64.wast', 5, '*', 'shared-wrong'): ('#1209', 1),
    ('load64.wast', 0, '*', 'parity-divergence/memory-only'): ('#1209', 6),
    ('load64.wast', 0, '*', 'parity-divergence/opt-wrong'): ('#1209', 4),
    ('memory64.wast', 9, '*', 'parity-divergence/memory-only'): ('#1209', 40),
    ('memory64.wast', 9, '*', 'shared-wrong'): ('#1209', 1),
    ('memory_copy64.wast', 0, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_copy64.wast', 0, '*', 'shared-wrong/memory'): ('#1209', 22),
    ('memory_copy64.wast', 1, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_copy64.wast', 1, '*', 'shared-wrong/memory'): ('#1209', 22),
    ('memory_copy64.wast', 2, '*', 'shared-wrong'): ('#1209', 11),
    ('memory_copy64.wast', 2, '*', 'shared-wrong/memory'): ('#1209', 20),
    ('memory_copy64.wast', 3, '*', 'shared-wrong'): ('#1209', 6),
    ('memory_copy64.wast', 3, '*', 'shared-wrong/memory'): ('#1209', 25),
    ('memory_copy64.wast', 4, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_copy64.wast', 4, '*', 'shared-wrong/memory'): ('#1209', 22),
    ('memory_copy64.wast', 5, '*', 'shared-wrong'): ('#1209', 11),
    ('memory_copy64.wast', 5, '*', 'shared-wrong/memory'): ('#1209', 20),
    ('memory_copy64.wast', 6, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_copy64.wast', 6, '*', 'shared-wrong/memory'): ('#1209', 22),
    ('memory_copy64.wast', 7, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_copy64.wast', 7, '*', 'shared-wrong/memory'): ('#1209', 22),
    ('memory_grow64.wast', 0, '*', 'parity-divergence/both-wrong-differently'): ('#1209', 2),
    ('memory_grow64.wast', 0, '*', 'parity-divergence/opt-wrong'): ('#1209', 1),
    ('memory_grow64.wast', 1, '*', 'shared-wrong'): ('#1209', 6),
    ('memory_grow64.wast', 2, '*', 'shared-wrong'): ('#1209', 6),
    ('memory_grow64.wast', 3, '*', 'shared-wrong'): ('#1209', 10),
    ('memory_init64.wast', 0, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_init64.wast', 0, '*', 'shared-wrong/memory'): ('#1209', 22),
    ('memory_init64.wast', 1, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_init64.wast', 1, '*', 'shared-wrong/memory'): ('#1209', 21),
    ('memory_init64.wast', 2, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_init64.wast', 2, '*', 'shared-wrong/memory'): ('#1209', 21),
    ('memory_init64.wast', 3, '*', 'shared-wrong'): ('#1209', 9),
    ('memory_init64.wast', 3, '*', 'shared-wrong/memory'): ('#1209', 21),
    # #1210 — a value live across a call inside a value-carrying block/if/loop is
    # lost on BOTH selectors (parity-blind; caught by the wasmtime leg).
    ('block.wast', 0, 'as-binary-operand', 'shared-wrong'): ('#1210', 1),
    ('block.wast', 0, 'as-binary-operands', 'shared-wrong'): ('#1210', 1),
    ('block.wast', 0, 'as-mixed-operands', 'shared-wrong'): ('#1210', 1),
    ('block.wast', 0, 'multi', 'shared-wrong'): ('#1210', 1),
    ('if.wast', 0, 'as-binary-operand', 'shared-wrong'): ('#1210', 4),
    ('if.wast', 0, 'as-binary-operands', 'shared-wrong'): ('#1210', 2),
    ('if.wast', 0, 'as-call_indirect-last', 'shared-wrong'): ('#1210', 1),
    ('if.wast', 0, 'as-call_indirect-mid', 'shared-wrong'): ('#1210', 2),
    ('if.wast', 0, 'as-mixed-operands', 'shared-wrong'): ('#1210', 2),
    ('if.wast', 0, 'as-select-last', 'shared-wrong'): ('#1210', 2),
    ('if.wast', 0, 'as-select-mid', 'shared-wrong'): ('#1210', 2),
    ('local_tee.wast', 0, 'as-block-first', 'shared-wrong'): ('#1210', 1),
    ('local_tee.wast', 0, 'as-block-mid', 'shared-wrong'): ('#1210', 1),
    ('local_tee.wast', 0, 'as-loop-first', 'shared-wrong'): ('#1210', 1),
    ('local_tee.wast', 0, 'as-loop-mid', 'shared-wrong'): ('#1210', 1),
    ('loop.wast', 0, 'as-binary-operand', 'shared-wrong'): ('#1210', 1),
    ('loop.wast', 0, 'as-binary-operands', 'shared-wrong'): ('#1210', 1),
    ('loop.wast', 0, 'as-mixed-operands', 'shared-wrong'): ('#1210', 1),
    ('loop.wast', 0, 'multi', 'shared-wrong'): ('#1210', 1),
    ('select.wast', 0, 'as-loop-first', 'shared-wrong'): ('#1210', 2),
    ('select.wast', 0, 'as-loop-mid', 'shared-wrong'): ('#1210', 2),
    ('stack.wast', 0, 'not-quite-a-tree', 'shared-wrong'): ('#1210', 2),
    # #1215 — br_table/br_if with a value-carrying branch or if in an operand
    # position, wrong on both selectors.
    ('br.wast', 0, 'nested-br_table-value-index', 'shared-wrong'): ('#1215', 1),
    ('br_if.wast', 0, 'nested-br_table-value-index', 'shared-wrong'): ('#1215', 2),
    ('br_table.wast', 0, 'as-loop-first', 'shared-wrong'): ('#1215', 1),
    ('br_table.wast', 0, 'as-loop-last', 'shared-wrong'): ('#1215', 1),
    ('br_table.wast', 0, 'as-loop-mid', 'shared-wrong'): ('#1215', 1),
    ('br_table.wast', 0, 'nested-br_table-value', 'shared-wrong'): ('#1215', 2),
    ('br_table.wast', 0, 'nested-br_table-value-index', 'shared-wrong'): ('#1215', 5),
    ('func.wast', 0, 'break-br_table-nested-num', 'shared-wrong'): ('#1215', 1),
    ('func.wast', 0, 'break-br_table-num', 'shared-wrong'): ('#1215', 4),
    ('if.wast', 0, 'as-br_if-last', 'shared-wrong'): ('#1215', 1),
    ('if.wast', 0, 'as-br_table-last', 'shared-wrong'): ('#1215', 2),
    # #1214 — i64 read-before-write local not zero-initialised on either selector.
    ('func.wast', 0, 'init-local-i64', 'shared-wrong'): ('#1214', 1),
    # #1211 — call_indirect ignores a non-zero table index (wrong callee);
    # elem.wast call_in_table lands on a non-code address.
    ('call_indirect.wast', 1, 'call-1', 'shared-wrong'): ('#1211', 2),
    ('call_indirect.wast', 1, 'call-2', 'shared-wrong'): ('#1211', 3),
    ('call_indirect.wast', 1, 'call-3', 'shared-wrong'): ('#1211', 2),
    ('elem.wast', 72, 'call_in_table', 'shared-wrong'): ('#1211', 1),
    ('elem.wast', 73, 'call_in_table', 'shared-wrong'): ('#1211', 1),
    ('elem.wast', 74, 'call_in_table', 'shared-wrong'): ('#1211', 1),
    # memory.grow in a fixed-SRAM self-contained image returns -1 — a spec-LEGAL
    # failure (#539 lineage), while wasmtime grows; the later `memory.size` and
    # `check-memory-zero` results follow from it. Recorded with this reason, no
    # issue: the divergence is a capability boundary, not a miscompile.
    ('block.wast', 0, 'as-memory.grow-value', 'shared-wrong'): ('#539-grow-fails', 1),
    ('call.wast', 0, 'as-memory.grow-value', 'shared-wrong'): ('#539-grow-fails', 1),
    ('if.wast', 0, 'as-memory.grow-value', 'shared-wrong'): ('#539-grow-fails', 2),
    ('load.wast', 0, 'as-memory.grow-size', 'shared-wrong'): ('#539-grow-fails', 1),
    ('local_tee.wast', 0, 'as-memory.grow-size', 'shared-wrong'): ('#539-grow-fails', 1),
    ('loop.wast', 0, 'as-memory.grow-value', 'shared-wrong'): ('#539-grow-fails', 1),
    ('memory_size.wast', 0, 'size', 'shared-wrong'): ('#539-grow-fails', 3),
    ('memory_size.wast', 1, 'size', 'shared-wrong'): ('#539-grow-fails', 3),
    ('memory_size.wast', 2, 'size', 'shared-wrong'): ('#539-grow-fails', 4),
    ('memory_size.wast', 3, 'size', 'shared-wrong'): ('#539-grow-fails', 5),
    ('nop.wast', 0, 'as-memory.grow-everywhere', 'shared-wrong'): ('#539-grow-fails', 1),
    ('nop.wast', 0, 'as-memory.grow-first', 'shared-wrong'): ('#539-grow-fails', 1),
    ('nop.wast', 0, 'as-memory.grow-last', 'shared-wrong'): ('#539-grow-fails', 1),
    ('select.wast', 0, 'as-memory.grow-value', 'shared-wrong'): ('#539-grow-fails', 2),
}
# Divergence kinds that are recorded but never gate: the reference vs the
# .wast literal is not a synth verdict; a mismatch AFTER an OOB trap the
# default image does not honour is the envelope's state cascade (the legs
# still agree with each other, which IS the parity check); and two legs
# disagreeing on how an OOB access misbehaves (fault vs garbage value) is
# undefined behaviour under `SafetyBounds::None`, not a lowering difference.
INFORMATIONAL_KINDS = {"reference-vs-literal", "shared-wrong-after-trap-miss",
                       "shared-wrong-after-trap-miss/memory", "trap-parity-envelope"}

SKIP_RE = re.compile(r"warning: skipping function '((?:[^'\\]|\\.)*)': (.*)")
PATH_RE = re.compile(
    r"\[path-debug\] (optimized \(ir_to_arm ok\)|direct \(pre-gate\)|direct \(fallback: .*?\))"
    r" func=(\d+|\?)(?: reasons=(\S*))?$",
    re.MULTILINE,
)


# ---------------------------------------------------------------------------
# .wast reader — top-level forms in file order, with comments and strings
# handled (a regex cannot: the forms nest, and comments contain parens).
# ---------------------------------------------------------------------------
def _skip_block_comment(t: str, i: int) -> int:
    depth, n = 0, len(t)
    while i < n:
        if t.startswith("(;", i):
            depth += 1
            i += 2
        elif t.startswith(";)", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        else:
            i += 1
    return n


def _scan_form(t: str, i: int) -> int:
    """`t[i] == '('` -> index of the matching ')'."""
    depth, n = 0, len(t)
    while i < n:
        c = t[i]
        if c == '"':
            i += 1
            while i < n and t[i] != '"':
                i += 2 if t[i] == "\\" else 1
            i += 1
            continue
        if t.startswith(";;", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
            continue
        if t.startswith("(;", i):
            i = _skip_block_comment(t, i)
            continue
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError("unbalanced form")


def top_forms(t: str) -> list[str]:
    out, i, n = [], 0, len(t)
    while i < n:
        c = t[i]
        if c.isspace():
            i += 1
        elif t.startswith(";;", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
        elif t.startswith("(;", i):
            i = _skip_block_comment(t, i)
        elif c == "(":
            j = _scan_form(t, i)
            out.append(t[i : j + 1])
            i = j + 1
        else:
            i += 1
    return out


def parse_sexp(t: str):
    """Minimal s-expression reader: lists, atoms (str) and strings (bytes)."""
    pos = 0
    n = len(t)

    def ws():
        nonlocal pos
        while pos < n:
            if t[pos].isspace():
                pos += 1
            elif t.startswith(";;", pos):
                j = t.find("\n", pos)
                pos = n if j < 0 else j
            elif t.startswith("(;", pos):
                pos = _skip_block_comment(t, pos)
            else:
                break

    def read():
        nonlocal pos
        ws()
        if pos >= n:
            raise ValueError("eof")
        c = t[pos]
        if c == "(":
            pos += 1
            items = []
            while True:
                ws()
                if t[pos] == ")":
                    pos += 1
                    return items
                items.append(read())
        if c == '"':
            pos += 1
            start = pos
            while t[pos] != '"':
                pos += 2 if t[pos] == "\\" else 1
            raw = t[start:pos]
            pos += 1
            return WastStr(raw)
        start = pos
        while pos < n and not t[pos].isspace() and t[pos] not in "()":
            pos += 1
        return t[start:pos]

    return read()


class WastStr:
    """A string literal, decoded per the wast escape rules."""

    def __init__(self, raw: str):
        self.raw = raw
        out = bytearray()
        i = 0
        while i < len(raw):
            c = raw[i]
            if c != "\\":
                out += c.encode("utf-8")
                i += 1
                continue
            e = raw[i + 1]
            if e == "n":
                out.append(10)
            elif e == "t":
                out.append(9)
            elif e == "r":
                out.append(13)
            elif e in "\\'\"":
                out.append(ord(e))
            elif e == "u":
                j = raw.index("}", i)
                out += chr(int(raw[i + 3 : j].replace("_", ""), 16)).encode("utf-8")
                i = j + 1
                continue
            else:
                out.append(int(raw[i + 1 : i + 3], 16))
                i += 3
                continue
            i += 2
        self.bytes = bytes(out)

    def text(self) -> str:
        return self.bytes.decode("utf-8", errors="replace")


class Decl(Exception):
    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


def parse_const(form) -> tuple[str, int]:
    """`['i32.const', '-5']` -> ('i32', 0xFFFFFFFB). Floats/refs decline."""
    if not isinstance(form, list) or not form:
        raise Decl("non-const-arg")
    head = form[0]
    if head in ("i32.const", "i64.const"):
        raw = form[1].replace("_", "")
        neg = raw.startswith("-")
        raw = raw.lstrip("+-")
        v = int(raw, 0)
        if neg:
            v = -v
        bits = 32 if head == "i32.const" else 64
        return head[:3], v & ((1 << bits) - 1)
    if head in ("f32.const", "f64.const"):
        raise Decl("float-abi")
    if head.startswith("ref.") or head in ("v128.const",):
        raise Decl("ref-type" if head.startswith("ref.") else "simd")
    raise Decl(f"unknown-const:{head}")


# ---------------------------------------------------------------------------
# Compilation — one leg
# ---------------------------------------------------------------------------
class LegBuild:
    def __init__(self, name: str, ok: bool, elf: Path | None, funcs: set[str],
                 skipped: dict[str, str], module_error: str, paths: list[tuple]):
        self.name = name
        self.ok = ok
        self.elf = elf
        self.funcs = funcs            # exported functions present in the image
        self.skipped = skipped        # name -> machine reason
        self.module_error = module_error
        self.paths = paths            # (kind, func_idx, reasons) from SYNTH_PATH_DEBUG


def compile_leg(name: str, extra: list[str], src: Path, tmp: Path) -> LegBuild:
    out = tmp / f"{name}.elf"
    r = subprocess.run(
        [SYNTH, "compile", str(src), "--target", "cortex-m4", "--all-exports",
         "--allow-skipped-exports", "-o", str(out)] + extra,
        capture_output=True, text=True, timeout=300,
        env=dict(os.environ, SYNTH_PATH_DEBUG="1"),
    )
    err = r.stdout + r.stderr
    skipped = {}
    for m in SKIP_RE.finditer(err):
        skipped[m.group(1)] = m.group(2).strip()[:160]
    paths = []
    for m in PATH_RE.finditer(err):
        paths.append((m.group(1), m.group(2), m.group(3) or ""))
    if "panicked" in err:
        return LegBuild(name, False, None, set(), skipped, "PANIC: " + err[-300:], paths)
    if r.returncode != 0 or not out.exists():
        msg = next((l for l in err.splitlines() if l.startswith("Error")), err[-200:])
        return LegBuild(name, False, None, set(), skipped, msg.strip()[:240], paths)
    with out.open("rb") as fh:
        elf = ELFFile(fh)
        st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        funcs = {s.name for s in st.iter_symbols()
                 if s.name and s["st_info"]["type"] == "STT_FUNC"}
    funcs -= {"Reset_Handler", "Default_Handler", "Trap_Handler"}
    return LegBuild(name, True, out, funcs, skipped, "", paths)


def function_bytes(elf_path: Path) -> dict[str, bytes]:
    with elf_path.open("rb") as fh:
        elf = ELFFile(fh)
        st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        text = elf.get_section_by_name(".text")
        base, data = text["sh_addr"], text.data()
        out = {}
        for s in st.iter_symbols():
            if s.name and s["st_info"]["type"] == "STT_FUNC" and s["st_size"]:
                off = (s["st_value"] & ~1) - base
                out[s.name] = data[off : off + s["st_size"]]
        return out


# ---------------------------------------------------------------------------
# Execution — one image under unicorn, booted through its own Reset_Handler
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
        text_va, _, text = min(segs, key=lambda s: s[0])
        sp0, reset = struct.unpack_from("<II", text, 0)
        self.sp0 = sp0
        ram = [(va, sz) for va, sz, _ in segs if va != text_va]
        ram_lo = min((va for va, _ in ram), default=sp0 - 0x20000) & ~0xFFF
        ram_hi = max(sp0, max((va + sz for va, sz in ram), default=0))
        ram_hi = (ram_hi + 0xFFF) & ~0xFFF
        mu.mem_map(text_va & ~0xFFF, ((text_va + len(text) + 0xFFF) & ~0xFFF) - (text_va & ~0xFFF))
        mu.mem_write(text_va, text)
        mu.mem_map(ram_lo, ram_hi - ram_lo)
        for va, _, data in segs:
            if va != text_va and data:
                mu.mem_write(va, data)
        mu.mem_map(RET & ~0xFFF, 0x1000)
        mu.reg_write(UC_ARM_REG_SP, sp0)
        # Boot: run the shipped startup up to (not including) its `blx r0`
        # into the entry function. Thumb-decode forward from the reset vector
        # so a 32-bit immediate that happens to contain 0x4780 cannot fool it.
        pc = reset & ~1
        while True:
            hw = struct.unpack_from("<H", text, pc - text_va)[0]
            if hw == 0x4780:
                break
            pc += 4 if (hw >> 11) in (0b11101, 0b11110, 0b11111) else 2
        self.entry_blx = pc
        mu.emu_start(reset | 1, pc, count=INSN_LIMIT)
        self.regs = {r: mu.reg_read(r) & M32 for r in (UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11)}
        self.mem_base = self.regs[UC_ARM_REG_R11]
        self.mem_size = self.regs[UC_ARM_REG_R10]
        self.trapped = False
        trap = self.syms.get("Trap_Handler", 0) & ~1

        def on_trap_handler(uc, addr, size, _):
            self.trapped = True
            uc.emu_stop()

        def on_intr(uc, intno, _):
            self.trapped = True
            uc.emu_stop()

        if trap:
            mu.hook_add(UC_HOOK_CODE, on_trap_handler, begin=trap, end=trap + 1)
        mu.hook_add(UC_HOOK_INTR, on_intr)

    def call(self, fn: str, words: list[int], result_words: int):
        """-> ('ok', [words]) | ('trap',) | ('fault', msg) | ('timeout',) plus
        a list of contract violations (callee-saved R9/R10/R11, SP balance)."""
        mu = self.mu
        addr = self.syms[fn]
        for r, w in zip(ARG_REGS, words):
            mu.reg_write(r, w & M32)
        mu.reg_write(UC_ARM_REG_SP, self.sp0)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        self.trapped = False
        try:
            mu.emu_start(addr | 1, RET, count=INSN_LIMIT)
        except UcError as e:
            return ("fault", str(e)), []
        if self.trapped:
            return ("trap",), []
        if (mu.reg_read(UC_ARM_REG_PC) & ~1) != RET:
            return ("timeout",), []
        viol = []
        for r, name in ((UC_ARM_REG_R9, "R9"), (UC_ARM_REG_R10, "R10"), (UC_ARM_REG_R11, "R11")):
            got = mu.reg_read(r) & M32
            if got != self.regs[r]:
                viol.append(f"{name} clobbered: 0x{got:08x} != 0x{self.regs[r]:08x}")
                mu.reg_write(r, self.regs[r])
        sp = mu.reg_read(UC_ARM_REG_SP) & M32
        if sp != self.sp0:
            viol.append(f"SP imbalance: 0x{sp:08x} != 0x{self.sp0:08x}")
        res = [mu.reg_read(r) & M32 for r in ARG_REGS[:result_words]]
        return ("ok", res), viol

    def memory(self) -> bytes:
        if not self.mem_size:
            return b""
        return bytes(self.mu.mem_read(self.mem_base, self.mem_size))


# ---------------------------------------------------------------------------
# wasmtime — the reference engine
# ---------------------------------------------------------------------------
def to_signed(v: int, bits: int) -> int:
    return v - (1 << bits) if v >= (1 << (bits - 1)) else v


class Reference:
    def __init__(self, engine, wat: str):
        self.store = wasmtime.Store(engine)
        module = wasmtime.Module(engine, wat)
        self.inst = wasmtime.Instance(self.store, module, [])
        self.exports = self.inst.exports(self.store)
        # Any exported memory, whatever its name (spec modules export
        # `memory`, `mem`, `m`, ...).
        self.mem = next((v for _, v in self.exports.items() if isinstance(v, wasmtime.Memory)), None)

    def signature(self, fn: str) -> tuple[list[str], list[str]]:
        f = self.exports[fn]
        if not isinstance(f, wasmtime.Func):
            raise Decl("not-a-function")
        ft = f.type(self.store)
        return [str(t) for t in ft.params], [str(t) for t in ft.results]

    def call(self, fn: str, args: list[tuple[str, int]], results: list[str]):
        """-> ('ok', [unsigned 32-bit words]) | ('trap',)"""
        f = self.exports[fn]
        pyargs = [to_signed(v, 32 if t == "i32" else 64) for t, v in args]
        try:
            r = f(self.store, *pyargs)
        except wasmtime.Trap:
            return ("trap",)
        vals = [] if r is None else (r if isinstance(r, list) else [r])
        words = []
        for t, v in zip(results, vals):
            if t == "i64":
                words += [v & M32, (v >> 32) & M32]
            else:
                words.append(v & M32)
        return ("ok", words)

    def memory(self, size: int) -> bytes | None:
        if self.mem is None:
            return None
        have = self.mem.data_len(self.store)
        return bytes(self.mem.read(self.store, 0, min(size, have)))


# ---------------------------------------------------------------------------
# Per-module driver
# ---------------------------------------------------------------------------
def marshal_args(args: list[tuple[str, int]]) -> list[int]:
    """AAPCS: i32 -> one word; i64 -> an even-aligned pair. > 4 words declines
    (stack args are a separate contract this oracle does not execute)."""
    words: list[int] = []
    for t, v in args:
        if t == "i32":
            words.append(v)
        else:
            if len(words) % 2:
                words.append(0)
            words += [v & M32, (v >> 32) & M32]
    if len(words) > 4:
        raise Decl("stack-args")
    return words


def fmt_val(res) -> str:
    if res[0] == "ok":
        return "(" + ",".join(f"0x{w & M64:x}" if isinstance(w, int) else str(w) for w in res[1]) + ")"
    return res[0] + (f":{res[1]}" if len(res) > 1 else "")


class ModuleRun:
    """Everything one `(module ...)` form contributes to the ledger."""

    def __init__(self, file: str, idx: int):
        self.file, self.idx = file, idx
        self.legs: dict[str, LegBuild] = {}
        self.both = False
        self.decline = ""                    # module-level reason (if any)
        self.verdicts: Counter = Counter()
        self.declined: Counter = Counter()
        self.divergences: list[dict] = []    # executed disagreements
        self.accept_divergence: list[dict] = []  # one leg declined a function
        self.differing_funcs = 0
        self.identical_funcs = 0
        self.emulations = 0
        self.trap_miss = False
        self.mixed = False
        # RQ-65-MVPCORE (#1017): the module declares a `(start ...)`. Since the
        # self-contained Cortex-M image invokes it from Reset_Handler (before
        # the boot stops at the entry `blx r0`), a start module is executed
        # like any other — wasmtime runs start at instantiation, both images
        # run it in their own shipped startup, and the assertions that depend
        # on its side effects (start.wast: `get` reads what `inc` wrote) then
        # compare. Before this the oracle DECLINED every start module; the
        # floor below is what makes "the start function ran" a checked claim.
        self.has_start = False


def run_module(engine, file: str, idx: int, wat: str, actions: list, tmp: Path) -> ModuleRun:
    mr = ModuleRun(file, idx)
    src = tmp / f"m{idx}.wat"
    src.write_text(wat)
    sexp = parse_sexp(wat)
    kinds = [f[0] for f in sexp[1:] if isinstance(f, list) and f]
    if len(sexp) > 1 and isinstance(sexp[1], str) and sexp[1] in ("binary", "quote", "definition", "instance"):
        mr.decline = "binary-module"
        return mr
    if "import" in kinds:
        mr.decline = "imports"
        return mr
    # RQ-65-MVPCORE (#1017): a `(start ...)` module is no longer declined —
    # the ARM self-contained image invokes the start function from its own
    # Reset_Handler, and that is exactly what the boot below executes.
    mr.has_start = "start" in kinds
    for name, extra in LEGS:
        mr.legs[name] = compile_leg(name, extra, src, tmp)
    opt, direct = mr.legs["optimized"], mr.legs["direct"]
    if not (opt.ok and direct.ok):
        # module-level: one or both refused the whole module
        mr.decline = "module-decline:" + ";".join(
            f"{l.name}={l.module_error[:120]}" for l in (opt, direct) if not l.ok)
        if opt.ok != direct.ok:
            mr.accept_divergence.append(dict(func="<module>", accepted_by=opt.name if opt.ok else direct.name,
                                             reason=(direct if opt.ok else opt).module_error[:200]))
        return mr
    common = opt.funcs & direct.funcs
    for fn in sorted(opt.funcs ^ direct.funcs):
        acc = "optimized" if fn in opt.funcs else "direct"
        dec = direct if acc == "optimized" else opt
        mr.accept_divergence.append(dict(func=fn, accepted_by=acc,
                                         reason=dec.skipped.get(fn, "(no skip line — helper?)")))
    if not common:
        mr.decline = "no-common-function"
        return mr
    mr.both = True
    ob, db = function_bytes(opt.elf), function_bytes(direct.elf)
    for fn in common:
        if ob.get(fn) == db.get(fn):
            mr.identical_funcs += 1
        else:
            mr.differing_funcs += 1
    path_kinds = {k for k, _, _ in opt.paths}
    mr.mixed = ("optimized (ir_to_arm ok)" in path_kinds) and any(k.startswith("direct") for k in path_kinds)

    try:
        ref = Reference(engine, wat)
    except Exception as e:  # imports we did not catch, or wasmtime refusing
        mr.decline = "wasmtime-instantiate:" + str(e).splitlines()[0][:120]
        return mr
    ref_mem = ref.mem
    imgs = {}
    for name in ("optimized", "direct"):
        try:
            imgs[name] = Image(mr.legs[name].elf)
            mr.emulations += 1
        except UcError as e:
            mr.decline = f"boot-fault:{name}:{e}"
            return mr
    # Lock-step: the three engines share one action sequence. An action that
    # cannot be executed on ALL of them (a declined shape) is executed on NONE
    # — so the three stay consistent with EACH OTHER by construction, and the
    # comparison that matters (legs vs wasmtime, leg vs leg) survives a skip.
    # Only the .wast literal can be left behind by a skipped state mutation,
    # and that is the informational `reference-vs-literal` count, never a
    # verdict. The one asymmetric case — a trap wasmtime took and the legs did
    # not — is tracked by `trap_miss`.
    for act in actions:
        kind = act[0]
        if kind == "assert_exhaustion":
            mr.declined["exhaustion"] += 1
            continue
        try:
            # `(invoke "f" …)` stands alone as a state-mutating step; the
            # assert_* forms wrap it as their first operand.
            action = act if kind == "invoke" else (act[1] if len(act) > 1 else None)
            if not isinstance(action, list) or action[0] != "invoke":
                raise Decl("get-action" if isinstance(action, list) and action[0] == "get" else "no-invoke")
            if isinstance(action[1], str) and action[1].startswith("$"):
                raise Decl("named-module")
            fn = action[1].text()
            args = [parse_const(a) for a in action[2:]]
            expect = None
            if kind == "assert_return":
                exp = [parse_const(e) for e in act[2:]]
                if len(exp) > 1:
                    raise Decl("multi-value")
                expect = exp
            if fn not in common:
                if fn in (opt.funcs | direct.funcs):
                    raise Decl("symbol-missing")
                raise Decl("symbol-unknown")
            params, results = ref.signature(fn)
            if any(t not in ("i32", "i64") for t in params + results):
                raise Decl("float-abi" if any(t in ("f32", "f64") for t in params + results) else "ref-type")
            if len(results) > 1:
                raise Decl("multi-value")
            if len(params) != len(args):
                raise Decl("arity")
            words = marshal_args(args)
        except Decl as e:
            mr.declined[e.reason] += 1
            continue

        result_words = 2 if results == ["i64"] else len(results)
        outs = {"wasmtime": ref.call(fn, args, results)}
        viols = {}
        for name, img in imgs.items():
            res, viol = img.call(fn, words, result_words)
            mr.emulations += 1
            outs[name] = res
            viols[name] = viol

        o, d, w = outs["optimized"], outs["direct"], outs["wasmtime"]
        detail = f"{file} m{idx} {fn}({','.join(f'0x{v:x}' for _, v in args)}): " \
                 f"wasmtime={fmt_val(w)} optimized={fmt_val(o)} direct={fmt_val(d)}"
        # memory images
        mem_note = ""
        om, dm = imgs["optimized"].memory(), imgs["direct"].memory()
        if om != dm:
            n = min(len(om), len(dm))
            i = next((k for k in range(n) if om[k] != dm[k]), n)
            mem_note = f" MEM differs @+0x{i:x}: optimized=0x{om[i]:02x} direct=0x{dm[i]:02x}" if i < n \
                else f" MEM size differs {len(om)} vs {len(dm)}"
        ref_mem_note = ""
        if ref_mem is not None and w[0] == "ok" and om == dm and om:
            rm = bytes(ref_mem.read(ref.store, 0, min(len(om), ref_mem.data_len(ref.store))))
            if rm != om[: len(rm)]:
                i = next(k for k in range(len(rm)) if rm[k] != om[k])
                ref_mem_note = f" MEM vs wasmtime @+0x{i:x}: synth=0x{om[i]:02x} wasmtime=0x{rm[i]:02x}"
        vnote = "".join(f" [{n}: {'; '.join(v)}]" for n, v in viols.items() if v)

        if kind == "assert_trap" or (kind == "assert_return" and w[0] == "trap"):
            if w[0] != "trap":
                # wasmtime did not trap where the file says it should: the
                # reference disagrees with the spec text — harness-level
                # anomaly, recorded loudly.
                mr.declined["reference-no-trap"] += 1
                continue
            if o == d and o[0] not in ("trap", "fault"):
                # Neither leg trapped (the compliance envelope — no OOB trap
                # by default). The legs stay in lock-step with EACH OTHER;
                # only wasmtime's state is now ahead of them.
                mr.verdicts["trap-miss"] += 1
                mr.trap_miss = True
                continue
            if o[0] in ("trap", "fault") and d[0] in ("trap", "fault"):
                mr.verdicts["ok"] += 1
                # a trap leaves memory partially written on neither side
                continue
            # The legs DISAGREE about trapping. For an out-of-bounds access
            # that is the envelope (no bounds check by default: whether the
            # stray address faults or reads garbage depends on where each
            # path's addressing lands) — recorded, not gated. Any other trap
            # (div by zero, overflow, unreachable, table/element) is a guard
            # one path emits and the other does not: a parity divergence.
            msg = act[-1].text() if isinstance(act[-1], WastStr) else ""
            if "out of bounds" in msg:
                mr.verdicts["trap-parity-envelope"] += 1
                mr.trap_miss = True
                mr.divergences.append(dict(kind="trap-parity-envelope", func=fn, detail=detail))
                continue
            mr.verdicts["parity-divergence"] += 1
            mr.divergences.append(dict(kind="parity-divergence/trap-parity", func=fn,
                                       detail=detail + mem_note + vnote))
            continue

        if expect and w[0] == "ok":
            # wasmtime-FIRST: the reference is what the legs are held to, and
            # the .wast literal is a fourth opinion on the reference itself —
            # a disagreement here is a harness/spec-text anomaly, never a
            # synth verdict, so it is counted separately and loudly.
            ew = [expect[0][1] & M32, (expect[0][1] >> 32) & M32] if result_words == 2 else [expect[0][1] & M32]
            if ew != w[1]:
                mr.declined["reference-vs-literal"] += 1
                mr.divergences.append(dict(kind="reference-vs-literal", func=fn,
                                           detail=detail + f" literal={fmt_val(('ok', ew))}"))
        # Register-contract violations (callee-saved R9/R10/R11, SP balance)
        # are their own category: the VALUE may still be right — the caller
        # that runs next is what breaks — so they must not hide inside a
        # value verdict in either direction.
        if vnote:
            legs_v = [n for n, v in viols.items() if v]
            mr.verdicts["contract-violation"] += 1
            mr.divergences.append(dict(kind="contract-violation/" + "+".join(legs_v), func=fn,
                                       detail=detail + vnote))
            if o == d and o == w and om == dm:
                continue
        if o == d and om == dm and o == w:
            mr.verdicts["ok"] += 1
            if ref_mem_note:
                cat = "shared-wrong" if not mr.trap_miss else "shared-wrong-after-trap-miss"
                mr.verdicts[cat] += 1
                mr.divergences.append(dict(kind=cat + "/memory", func=fn, detail=detail + ref_mem_note))
            continue
        if o == d and om == dm:
            cat = "shared-wrong" if not mr.trap_miss else "shared-wrong-after-trap-miss"
            mr.verdicts[cat] += 1
            mr.divergences.append(dict(kind=cat, func=fn, detail=detail))
            continue
        sub = "opt-wrong" if d == w and o != w else "direct-wrong" if o == w and d != w else "both-wrong-differently"
        if o == d:
            sub = "memory-only"
        mr.verdicts["parity-divergence"] += 1
        mr.divergences.append(dict(kind=f"parity-divergence/{sub}", func=fn, detail=detail + mem_note))
    return mr


# ---------------------------------------------------------------------------
# Corpus walk
# ---------------------------------------------------------------------------
def modules_of(text: str):
    """Yield (module_index, module_text, [actions]) — each module with the
    assertions that follow it up to the next module."""
    cur = None
    idx = -1
    named_only = False
    for form in top_forms(text):
        head = form[1:].split(None, 1)[0].rstrip(")") if len(form) > 1 else ""
        if head == "module":
            if cur is not None:
                yield cur
            idx += 1
            cur = [idx, form, []]
        elif head in ("assert_return", "assert_trap", "invoke", "assert_exhaustion"):
            if cur is not None:
                try:
                    cur[2].append(parse_sexp(form))
                except Exception:
                    cur[2].append(["unparseable"])
        # register / assert_invalid / assert_malformed / assert_unlinkable /
        # assert_exception: no action for the engines
    if cur is not None:
        yield cur


def process_file(engine, wast: Path, jobs_tmp: Path) -> list[ModuleRun]:
    text = wast.read_text(errors="replace")
    runs = []
    with tempfile.TemporaryDirectory(dir=jobs_tmp) as td:
        for idx, mod_text, actions in modules_of(text):
            if not actions:
                mr = ModuleRun(wast.name, idx)
                mr.decline = "no-assertions"
                runs.append(mr)
                continue
            try:
                runs.append(run_module(engine, wast.name, idx, mod_text, actions, Path(td)))
            except Exception as e:  # never let one module kill the corpus walk
                mr = ModuleRun(wast.name, idx)
                mr.decline = f"harness-error:{type(e).__name__}:{str(e)[:120]}"
                runs.append(mr)
    return runs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-suite", action="store_true",
                    help="tests/wast only (LOCAL floors); default requires the spec-testsuite submodule")
    ap.add_argument("--only", help="substring filter on file name")
    ap.add_argument("-j", "--jobs", type=int, default=min(8, os.cpu_count() or 4))
    ap.add_argument("--json", help="write the full ledger here")
    args = ap.parse_args()

    files = sorted(WAST_DIR.glob("*.wast")) + OWN_FIXTURES
    if not args.no_suite:
        suite = sorted(SUITE_DIR.glob("*.wast"))
        if not suite:
            print(f"FAIL: {SUITE_DIR} is empty — checkout needs `submodules: recursive` "
                  f"(or pass --no-suite locally). A parity run over an empty corpus is vacuous.")
            return 1
        files += suite
    if args.only:
        files = [f for f in files if args.only in f.name]
    if not files:
        print("FAIL: no corpus files")
        return 1
    if not Path(SYNTH).is_file():
        print(f"FAIL: synth not found at {SYNTH}")
        return 1

    engine = wasmtime.Engine()
    runs: list[ModuleRun] = []
    with tempfile.TemporaryDirectory() as td, \
            concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for rs in ex.map(lambda f: process_file(engine, f, Path(td)), files):
            runs.extend(rs)

    # ---- ledger -----------------------------------------------------------
    verdicts, declined, module_declines = Counter(), Counter(), Counter()
    path_tally, pregate_reasons, fallback_reasons = Counter(), Counter(), Counter()
    accept_div, divergences = [], []
    actual_pins: Counter = Counter()   # (file, idx, func, kind) -> count, gating kinds only
    both = sum(1 for r in runs if r.both)
    differing = sum(r.differing_funcs for r in runs)
    identical = sum(r.identical_funcs for r in runs)
    emulations = sum(r.emulations for r in runs)
    mixed = sum(1 for r in runs if r.mixed and r.both)
    # RQ-65-MVPCORE (#1017): the start-function population, counted
    # separately so "start modules executed" is a number this run prints and
    # a floor below can refuse.
    start_modules = sum(1 for r in runs if r.has_start)
    start_both = sum(1 for r in runs if r.has_start and r.both)
    start_ok = sum(r.verdicts.get("ok", 0) for r in runs if r.has_start and r.both)
    for r in runs:
        verdicts.update(r.verdicts)
        declined.update(r.declined)
        if r.decline:
            module_declines[r.decline.split(":")[0]] += 1
        for d in r.divergences:
            divergences.append(f"{d['kind']}: {d['detail']}")
            if d["kind"] not in INFORMATIONAL_KINDS:
                actual_pins[(r.file, r.idx, d.get("func", "?"), d["kind"])] += 1
        for a in r.accept_divergence:
            accept_div.append(f"{r.file} m{r.idx} {a['func']}: only {a['accepted_by']} — {a['reason']}")
        opt = r.legs.get("optimized")
        if opt:
            for kind, fidx, reasons in opt.paths:
                if kind.startswith("optimized"):
                    path_tally["optimized"] += 1
                elif kind.startswith("direct (pre-gate"):
                    path_tally["direct (pre-gate)"] += 1
                    pregate_reasons[reasons or "?"] += 1
                else:
                    path_tally["direct (fallback)"] += 1
                    fallback_reasons[kind[len("direct (fallback: "):-1][:70]] += 1
    optimized_funcs = path_tally["optimized"]
    compared = sum(v for k, v in verdicts.items())

    print(f"#197 selector parity — {len(files)} files, {len(runs)} modules with assertions considered")
    print(f"  modules both legs accepted: {both}   (mixed-path images among them: {mixed})")
    print(f"  start-function modules: {start_modules} seen, {start_both} both-accepted and booted "
          f"through a Reset_Handler that invokes the start function, {start_ok} assertion(s) ok")
    print(f"  module-level declines: " + (", ".join(f"{k}={v}" for k, v in sorted(module_declines.items())) or "none"))
    print(f"  functions common to both legs: {differing + identical}  "
          f"(bytes differ: {differing}, byte-identical: {identical})")
    print(f"  optimized leg routing: " + ", ".join(f"{k}={v}" for k, v in sorted(path_tally.items())))
    print(f"    pre-gate reasons: " + (", ".join(f"{k}={v}" for k, v in pregate_reasons.most_common()) or "none"))
    print(f"    fallback reasons: " + (", ".join(f"{k}={v}" for k, v in fallback_reasons.most_common()) or "none"))
    print(f"  assertions executed on all three engines: {compared}")
    print(f"    verdicts: " + ", ".join(f"{k}={v}" for k, v in sorted(verdicts.items())))
    print(f"    declined by reason: " + (", ".join(f"{k}={v}" for k, v in sorted(declined.items())) or "none"))
    print(f"  accept/decline divergences (one leg only): {len(accept_div)}")
    for line in accept_div[:40]:
        print(f"    {line}")
    if len(accept_div) > 40:
        print(f"    ... and {len(accept_div) - 40} more (see --json)")
    print(f"  executed divergences: {len(divergences)}")
    for line in divergences[:60]:
        print(f"    {line}")
    if len(divergences) > 60:
        print(f"    ... and {len(divergences) - 60} more (see --json)")
    print(f"  emulator entries (harness count): {emulations}")

    if args.json:
        Path(args.json).write_text(json.dumps(dict(
            files=len(files), modules=len(runs), both=both, mixed=mixed,
            start_modules=start_modules, start_both=start_both, start_ok=start_ok,
            differing_funcs=differing, identical_funcs=identical,
            verdicts=verdicts, declined=declined, module_declines=module_declines,
            path_tally=path_tally, pregate_reasons=pregate_reasons, fallback_reasons=fallback_reasons,
            accept_divergences=accept_div, divergences=divergences,
            per_module=[dict(file=r.file, idx=r.idx, both=r.both, decline=r.decline, mixed=r.mixed,
                             verdicts=r.verdicts, declined=r.declined, differing=r.differing_funcs,
                             identical=r.identical_funcs, accept_divergence=r.accept_divergence,
                             divergences=r.divergences,
                             optimized_paths=[list(p) for p in r.legs["optimized"].paths] if "optimized" in r.legs else [],
                             skipped={n: l.skipped for n, l in r.legs.items()})
                        for r in runs],
        ), indent=1, default=str))

    floors = FLOORS_LOCAL if args.no_suite or args.only else FLOORS_FULL
    fails = []
    measured = dict(modules_both=both, assertions_compared=compared,
                    optimized_funcs=optimized_funcs, differing_funcs=differing)
    for k, floor in floors.items():
        if measured[k] < floor:
            fails.append(f"NON-VACUITY: {k} = {measured[k]} < floor {floor}")
    # RQ-65-MVPCORE (#1017): whenever start.wast is in the run, the start
    # population must have been EXECUTED, not declined — this is the floor
    # that was red on the pre-invocation compiler (both legs refused every
    # start module, #1046) and is what turned green when Reset_Handler began
    # calling the start function.
    if any(f.name == "start.wast" for f in files) and start_both < START_MODULES_FLOOR:
        fails.append(f"NON-VACUITY: start-function modules both-accepted and booted = "
                     f"{start_both} < floor {START_MODULES_FLOOR} (seen {start_modules}) — "
                     f"the start function is being declined, not executed")
    # Pins: every gating divergence must be a KNOWN one at EXACTLY its pinned
    # count; every KNOWN pin whose file was in this run must still be there.
    # A pin whose function is "*" covers a whole module (one class hitting
    # every function of a spec module, e.g. the 30 narrow-load functions of
    # address.wast m1) — still an exact count, over the module.
    ran_files = {f.name for f in files}
    wild = {k for k in KNOWN if k[2] == "*"}
    folded: Counter = Counter()
    for (f, i, fn, kind), n in actual_pins.items():
        wk = (f, i, "*", kind)
        folded[wk if wk in wild else (f, i, fn, kind)] += n
    actual_pins = folded
    pinned_ok = unpinned = 0
    for key, n in sorted(actual_pins.items()):
        if key in KNOWN and KNOWN[key][1] == n:
            pinned_ok += n
            continue
        unpinned += n
        if key in KNOWN:
            fails.append(f"PINNED DIVERGENCE MOVED: {key[0]} m{key[1]} {key[2]} {key[3]}: "
                         f"{n} != pinned {KNOWN[key][1]} ({KNOWN[key][0]}) — a fix landed or a new "
                         f"instance appeared; re-measure and move the pin in the same PR")
        else:
            fails.append(f"NEW DIVERGENCE (not pinned): {key[0]} m{key[1]} {key[2]} {key[3]} x{n}")
    for key, (issue, n) in KNOWN.items():
        if key[0] in ran_files and key not in actual_pins:
            fails.append(f"PINNED DIVERGENCE VANISHED: {key[0]} m{key[1]} {key[2]} {key[3]} "
                         f"(pinned {n}, {issue}) — the fix landed? move the pin, close on the release")
    # A harness exception is not a verdict: the oracle did NOT evaluate that
    # module. Green with a swallowed exception is the #911 shape, so any
    # count here is red (measured cause at authoring: the synth binary being
    # relinked by a concurrent `cargo test` in the same target dir).
    herr = [f"{r.file} m{r.idx}: {r.decline}" for r in runs if r.decline.startswith("harness-error")]
    if herr:
        fails.append(f"HARNESS ERROR on {len(herr)} module(s) — not evaluated: " + "; ".join(herr[:5]))
    hard = unpinned
    print(f"  pinned known divergences: {pinned_ok} assertion(s) across "
          f"{len([k for k in actual_pins if k in KNOWN])} pins; unpinned: {unpinned}")
    print(f"#197 CHECKS={compared - hard}/{compared} assertions in parity over {both} modules")
    if fails:
        for f in fails:
            print(f"FAIL: {f}")
        return 1
    print("RESULT: PASS — every assertion both selectors accepted agrees between them and with wasmtime")
    return 0


if __name__ == "__main__":
    sys.exit(main())
