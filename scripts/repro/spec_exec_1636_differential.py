#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 49121
"""RQ-90-SPECEXEC (#1636) — the official spec suite's `assert_return` and
`assert_trap` directives, EXECUTED on Cortex-M images under unicorn and held to
the spec's own expected results, against an exact ratchet baseline.

# The gap this closes

`spec-suite.yml` was a COMPILE census: 257 top-level `.wast` files, every
bucket exact-pinned, and not one directive executed. The two oracles that do
execute spec directives (#197 parity, cortex-m4 only; #928, tests/wast only)
grade against wasmtime or skip the suite, set floats aside, and — the gap this
lane exists for — neither ACCOUNTS for the directives it does not run: a
module synth refuses, a module with imports, a directive before the first
module, all vanish from their totals without a reason. #1570 found the same
silent-drop shape in synth-test's WastParser.

# The accounting equation (the core of this oracle)

The DENOMINATOR is every top-level `assert_return` and `assert_trap` in every
file, counted by an independent walk of the file (`directive_census`), never by
the executor. For every (leg, file):

    pass + fail + Σ not-representable[reason]  ==  denominator

and a run where that does not hold is RED (`ACCOUNTING`). Every directive
lands in exactly one bucket, attributed to its own line:

  pass   pass:value       the result's bits equal the .wast literal's bits
         pass:nan-class   a `nan:canonical` / `nan:arithmetic` pattern matched
         pass:trap        `assert_trap` and the image trapped
  fail   fail:wrong-value, fail:no-value (trap/fault/timeout where a value was
         expected), fail:missing-trap, fail:contract-violation (R4..R8,
         S16..S31, R9/R10/R11 or SP not preserved), fail:state-dependent-memory
         (the zeroed and garbage machine states left different linear
         memory), fail:wrong-vs-reference (see state-skew below)
  notrep:<reason>  not representable on this leg, and WHY — module-level
         (no-module, module-form:<kind>, imports, module-declined,
         wasmtime-instantiate, boot-fault, harness-error) or directive-level
         (symbol-missing, ref-type, multi-value, stack-args, either, simd,
         named-module, get-action, module-trap, arity, symbol-unknown,
         vfp-pool-overflow, f64-on-sp-target, float-on-soft-target,
         unparseable), plus three honest execution states:
           envelope:oob-unchecked  an `assert_trap "out of bounds memory
             access"` the image did not trap under `--safety-bounds none` —
             synth's documented default envelope (CLAUDE.md), not a defect;
           after-envelope  a directive that disagreed AFTER such a miss in the
             same module: the image wrote where wasmtime trapped, so the
             states have legitimately diverged (passes after it still pass);
           state-skew  wasmtime itself disagrees with a non-NaN literal (an
             action declined on BOTH engines left the module state behind the
             script) and the image AGREES with wasmtime. If the image disagrees
             with wasmtime too it is `fail:wrong-vs-reference`.

`synth-test stats` (the Rust `wast`-crate parser, #1570) is an independent
second count of the same files: with `SYNTH_TEST` set, every file's
`assert_return` total must equal this script's, so a parser regression on
either side is RED rather than a quietly smaller denominator.

# The legs (what executes, and why these)

  cortex-m4    the shipped no-FPU default (the integer population; every float
               function is declined by the compiler with GI-FPU-002 and lands
               in `notrep:symbol-missing`), default `--safety-bounds none`.
  cortex-m7dp  double-precision VFP: the only leg on which an f32/f64 directive
               can execute at all, marshalled by synth's AAPCS-VFP convention;
               built with `--safety-bounds software`, the spec-CONFORMANT
               configuration, so out-of-bounds `assert_trap`s GATE here instead
               of landing in the envelope.

Both are booted through the image's OWN shipped `Reset_Handler` (R9/R10/R11
contract and data-segment copy as synth emits them), self-contained,
`--all-exports --allow-skipped-exports`. RV32 and AArch64 are NOT legs: the
repo has no full-boot spec harness for either (the RV32 unicorn oracles are
per-fixture with a hand-seeded contract; AArch64 executes natively on the
macOS/arm64-linux jobs, not under unicorn), and building one is a lane of its
own. cortex-m4f is not a leg. MEASURED (compile-only, every module of the
suite on cortex-m4f vs cortex-m7dp at default bounds): its compiled function
set is a subset of cortex-m7dp's in every module but ONE — call.wast's module
at line 3, which cortex-m7dp refuses whole (#1102: a retained f32/f64 function
relocates against a declined one) and cortex-m4f compiles (52 functions).
Those directives run here on cortex-m4 only where they are integer-typed; the
float ones are a stated coverage residual, not worth a third leg's runtime.

The harness (boot, AAPCS-VFP marshalling, literal->bits by wasmtime's WAT
parser, zeroed+garbage machine states, callee-saved checks) is #1617's
FLOATEXEC runner (closed unmerged), lifted and generalised from "gate floats
only" to "gate every directive and account for every one". The .wast reader is
#197's, imported — one parser for the corpus, not a mirror.

# The ratchet baseline (KNOWN, below)

Every directive that FAILS today is pinned by its exact identity
`(leg, file, line, col, outcome)` -> issue, positions at the pinned
spec-testsuite submodule commit (the function name rides in a trailing
comment). The value is ONE string — an exact `#N` or a reason declared in
scripts/stale_pin_check.py's REASON_STRINGS — because stale_pin_check derives
every pin's owning issue from it and requires that issue to be OPEN. The 14
new wrong-code entries found by this oracle's first run name their own
issues: #1643 (call_indirect, 12) and #1642 (f64.store partial write, 2).
RED when:
  * a failure is not in KNOWN                       (NEW FAILURE)
  * a KNOWN entry's directive no longer fails       (BASELINE ENTRY NOW PASSES
    — remove it in the same PR; that removal is the fix's evidence)
  * a KNOWN entry fails with a different outcome    (BASELINE ENTRY MOVED)
The table may only shrink; it is listed in claims.yaml's
`known_open_pin_tables`, so it is pin debt under `known_open_pins` (direction
down) and its population is declared there.

# Non-vacuity

  * the corpus must hold exactly SUITE_FILES files and exactly
    DIRECTIVES_TOTAL in-scope directives (an emptied checkout or a reader
    regression is RED);
  * per leg, executed directives (pass + fail) >= EXECUTED_FLOOR[leg] — the
    measured count, never 0;
  * the accounting equation above, per (leg, file);
  * `# ci-checks: emulations` (oracle_run.py) counts real emulator entries.

Run (needs wasmtime==48.0.0 + unicorn==2.1.4 + pyelftools + the submodule):
  SYNTH=./target/debug/synth SYNTH_TEST=./target/debug/synth-test \\
      python3 scripts/repro/spec_exec_1636_differential.py
  ... --only i32 --leg cortex-m4        # a quick slice (floors not applied)
  ... --emit-baseline                   # print the KNOWN literal for review
"""

from __future__ import annotations

import argparse
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
from collections import Counter, defaultdict
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_HOOK_INTR, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as A

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SYNTH = os.environ.get("SYNTH", str(ROOT / "target" / "debug" / "synth"))
SYNTH_TEST = os.environ.get("SYNTH_TEST", "")
SUITE_DIR = ROOT / "tests" / "spec-testsuite"

# The .wast reader is #197's — ONE parser for the spec corpus, not a mirror.
_spec = importlib.util.spec_from_file_location("sp197", HERE / "selector_parity_197_differential.py")
sp197 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sp197)
parse_sexp, WastStr, Decl, SKIP_RE = sp197.parse_sexp, sp197.WastStr, sp197.Decl, sp197.SKIP_RE

# leg -> (synth --target, extra flags, double-precision VFP, has FPU, bounds checked)
LEGS = {
    "cortex-m4": ("cortex-m4", [], False, False, False),
    "cortex-m7dp": ("cortex-m7dp", ["--safety-bounds", "software"], True, True, True),
}
IN_SCOPE = ("assert_return", "assert_trap")
M32 = 0xFFFFFFFF
M64 = (1 << 64) - 1
RET = 0x00F0_0000
INSN_LIMIT = 4_000_000
POISON_WINDOW = 0x2000
MIN_POISON = 0x400
CORE_ARGS = [A.UC_ARM_REG_R0, A.UC_ARM_REG_R1, A.UC_ARM_REG_R2, A.UC_ARM_REG_R3]
SREG = [getattr(A, f"UC_ARM_REG_S{i}") for i in range(32)]
DREG = [getattr(A, f"UC_ARM_REG_D{i}") for i in range(16)]
CALLEE_SAVED_CORE = [getattr(A, f"UC_ARM_REG_R{i}") for i in range(4, 9)]
CONTRACT = [(A.UC_ARM_REG_R9, "R9"), (A.UC_ARM_REG_R10, "R10"), (A.UC_ARM_REG_R11, "R11")]

# ---------------------------------------------------------------------------
# NON-VACUITY — measured on the full corpus (see the RQ-90-SPECEXEC record).
# SUITE_FILES / DIRECTIVES_TOTAL are properties of the pinned submodule commit
# and move only with a submodule bump. EXECUTED_FLOOR is the measured count of
# executed (pass + fail) directives per leg: raise it when reach grows, never
# lower it to green a run.
# ---------------------------------------------------------------------------
SUITE_FILES = 257
DIRECTIVES_TOTAL = 57588
# RQ-90-CALLINDTYPE (#1643): 11636 -> 11634 and 24044 -> 24042. The fix
# makes type-rec.wast:183/192 (`run`) a LOUD closed-world decline on both
# legs (notrep:symbol-missing), where they had executed as missing-trap
# failures: the two directives per leg left the executed set for a named
# decline, not for a silent skip, and their 4 KNOWN entries left with them.
EXECUTED_FLOOR = {"cortex-m4": 11634, "cortex-m7dp": 24042}

# ---------------------------------------------------------------------------
# KNOWN — the ratchet baseline of FAILING directives.
# (leg, file, line, col, outcome) -> issue. Exact both directions.
# ---------------------------------------------------------------------------
KNOWN = {
    # #1643's 12 entries (type-rec.wast 183/192, type-subtyping.wast
    # 314/315/345/346, both legs) LEFT with RQ-90-CALLINDTYPE: the four
    # type-subtyping directives are pass:trap, the two type-rec `run`
    # directives a loud closed-world decline (notrep:symbol-missing).
    # #1642's 2 entries (memory_trap.wast 269/282, cortex-m7dp) LEFT with
    # RQ-90-F64STORE: f64.store's ONE bounds guard now covers all 8 bytes
    # before either word is written, so the reads after the straddling store
    # see untouched memory and both directives are pass:value.
    # #539-grow-fails — the fixed-SRAM image cannot grow linear memory, so
    # memory.grow returns -1. The spec PERMITS a failing grow; the spec SCRIPT
    # assumes success. An envelope, pinned (as #197 pins it) because each entry
    # still passes over an observed spec-script disagreement.
    ('cortex-m4', 'block.wast', 384, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m4', 'call.wast', 359, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m4', 'if.wast', 600, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m4', 'if.wast', 601, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m4', 'load.wast', 211, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-size
    ('cortex-m4', 'local_tee.wast', 345, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-size
    ('cortex-m4', 'loop.wast', 457, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m4', 'nop.wast', 380, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-first
    ('cortex-m4', 'nop.wast', 381, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-last
    ('cortex-m4', 'nop.wast', 382, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-everywhere
    ('cortex-m4', 'select.wast', 330, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m4', 'select.wast', 331, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m7dp', 'block.wast', 384, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m7dp', 'if.wast', 600, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m7dp', 'if.wast', 601, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m7dp', 'load.wast', 211, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-size
    ('cortex-m7dp', 'local_tee.wast', 345, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-size
    ('cortex-m7dp', 'loop.wast', 457, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m7dp', 'nop.wast', 380, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-first
    ('cortex-m7dp', 'nop.wast', 381, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-last
    ('cortex-m7dp', 'nop.wast', 382, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-everywhere
    ('cortex-m7dp', 'select.wast', 330, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    ('cortex-m7dp', 'select.wast', 331, 1, 'fail:wrong-value'): '#539-grow-fails',  # as-memory.grow-value
    # #539-grow-fails cascade — memory_size.wast reads memory.size after a grow
    # the fixed-SRAM image refused, so the size is the pre-grow size.
    ('cortex-m4', 'memory_size.wast', 9, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 11, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 13, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 23, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 25, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 27, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 39, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 41, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 43, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 45, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 55, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 57, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 59, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 61, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m4', 'memory_size.wast', 63, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 9, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 11, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 13, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 23, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 25, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 27, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 39, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 41, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 43, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 45, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 55, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 57, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 59, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 61, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
    ('cortex-m7dp', 'memory_size.wast', 63, 1, 'fail:wrong-value'): '#539-grow-fails',  # size
}


# ---------------------------------------------------------------------------
# The directive census — the denominator, independent of the executor
# ---------------------------------------------------------------------------
def top_forms_at(t: str):
    """[((line, col), form_text)] for every top-level form, in file order.
    (line, col) is the directive's IDENTITY: left-to-right.wast puts two
    directives on one line, so a line alone is not unique."""
    out, i, n, line = [], 0, len(t), 1
    last = 0
    while i < n:
        c = t[i]
        if c.isspace():
            i += 1
        elif t.startswith(";;", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
        elif t.startswith("(;", i):
            i = sp197._skip_block_comment(t, i)
        elif c == "(":
            line += t.count("\n", last, i)
            last = i
            col = i - t.rfind("\n", 0, i)
            j = sp197._scan_form(t, i)
            out.append(((line, col), t[i: j + 1]))
            i = j + 1
        else:
            i += 1
    return out


def head_of(form: str) -> str:
    m = re.match(r"\(\s*([^\s()]+)", form)
    return m.group(1) if m else ""


def directive_census(text: str) -> Counter:
    return Counter(head_of(f) for _, f in top_forms_at(text) if head_of(f) in IN_SCOPE)


def directive_positions(text: str) -> set:
    """The (line, col) of every in-scope directive — the accounting is a SET
    equality, so one dropped directive cannot be balanced by one stray."""
    return {pos for pos, f in top_forms_at(text) if head_of(f) in IN_SCOPE}


def synth_test_counts(path: Path):
    """synth-test's (Rust `wast` crate) assert_return count — the second parser."""
    r = subprocess.run([SYNTH_TEST, "stats", "--wast", str(path)], capture_output=True, text=True, timeout=120)
    if r.returncode != 0:
        return None
    m = re.search(r"Assert_return seen:\s+(\d+)", r.stdout)
    return int(m.group(1)) if m else None


# ---------------------------------------------------------------------------
# Literals -> bits, by wasmtime's own WAT parser (never Python float())
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
    return {key: ex[f"k{i}"](store) & (M32 if key[0] == "f32" else M64) for i, key in enumerate(lits)}


def value_of(form, bits: dict):
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
# AAPCS(-VFP) marshalling — synth's own convention (instruction_selector.rs)
# ---------------------------------------------------------------------------
def marshal(args, dp: bool, fpu: bool):
    core, taken, sregs = [], [False] * 16, []
    for ty, v in args:
        if ty in ("f32", "f64") and not fpu:
            raise Decl("float-on-soft-target")
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
        else:
            if len(core) % 2:
                core.append(None)
            core += [v & M32, (v >> 32) & M32]
    if len(core) > 4:
        raise Decl("stack-args")
    return core, sregs


# ---------------------------------------------------------------------------
# The image — booted through its own Reset_Handler (#1617's harness)
# ---------------------------------------------------------------------------
class Image:
    def __init__(self, elf_path: Path, fpu: bool):
        with elf_path.open("rb") as fh:
            elf = ELFFile(fh)
            st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
            self.syms = {s.name: s["st_value"] for s in st.iter_symbols() if s.name}
            segs = [(sg["p_vaddr"], sg["p_memsz"], sg.data())
                    for sg in elf.iter_segments() if sg["p_type"] == "PT_LOAD"]
        self.fpu = fpu
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
        # The shipped FPU-target startup enables the FPU itself by an RMW of
        # CPACR (SCB page); unicorn's FPU gate is the coprocessor register.
        mu.mem_map(0xE000E000, 0x1000)
        if fpu:
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
        top_data = max([va + sz for va, sz in ram if va + sz <= sp0] +
                       ([self.mem_base + self.mem_size] if self.mem_base + self.mem_size <= sp0 else []) +
                       [ram_lo])
        self.poison = (max(top_data, sp0 - POISON_WINDOW), sp0)
        plo, phi = self.poison
        r9 = self.boot[A.UC_ARM_REG_R9]
        if phi - plo < MIN_POISON:
            raise RuntimeError(f"poison window {phi - plo:#x} B < {MIN_POISON:#x} below SP {sp0:#x}")
        if self.mem_size and self.mem_base < phi and plo < self.mem_base + self.mem_size:
            raise RuntimeError("poison window overlaps linear memory")
        if plo <= r9 < phi:
            raise RuntimeError("poison window overlaps the R9 globals area")
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
        lo, hi = self.ram[0], self.poison[0]
        return bytes(self.mu.mem_read(lo, hi - lo))

    def restore(self, snap: bytes):
        self.mu.mem_write(self.ram[0], snap)

    def memory(self) -> bytes:
        if not self.mem_size:
            return b""
        return bytes(self.mu.mem_read(self.mem_base, self.mem_size))

    def call(self, fn, core, sregs, results, garbage: bool, rng: random.Random):
        mu = self.mu
        lo, hi = self.poison
        if garbage:
            pat = rng.randrange(3)
            if pat == 2:
                mu.mem_write(lo, rng.randbytes(hi - lo))
            else:
                mu.mem_write(lo, struct.pack("<I", (0x41414141, 0x7FC00001)[pat]) * ((hi - lo) // 4))
        else:
            mu.mem_write(lo, bytes(hi - lo))
        if self.fpu:
            for r in SREG:
                mu.reg_write(r, rng.getrandbits(32) if garbage else 0)
        for i in range(13):
            mu.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), rng.getrandbits(32) if garbage else 0)
        for r, _ in CONTRACT:
            mu.reg_write(r, self.boot[r])
        for r, w in zip(CORE_ARGS, core):
            if w is not None:
                mu.reg_write(r, w)
        for k, w in sregs:
            mu.reg_write(SREG[k], w)
        if self.fpu:
            mu.reg_write(A.UC_ARM_REG_FPSCR, 0)
        saved_core = {r: mu.reg_read(r) & M32 for r in CALLEE_SAVED_CORE}
        saved_vfp = {k: mu.reg_read(SREG[k]) & M32 for k in range(16, 32)} if self.fpu else {}
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
            if (mu.reg_read(r) & M32) != self.boot[r]:
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


def compile_image(src: Path, out: Path, leg: str):
    target, flags = LEGS[leg][0], LEGS[leg][1]
    r = subprocess.run([SYNTH, "compile", str(src), "--target", target, *flags, "--all-exports",
                        "--allow-skipped-exports", "-o", str(out)],
                       capture_output=True, text=True, timeout=300)
    err = r.stdout + r.stderr
    if "panicked" in err:
        return None, "PANIC: " + err[-300:]
    if r.returncode != 0 or not out.exists():
        msg = next((ln for ln in err.splitlines() if ln.startswith("Error")), err[-200:])
        return None, msg.strip()[:240]
    with out.open("rb") as fh:
        st = next(s for s in ELFFile(fh).iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        funcs = {s.name for s in st.iter_symbols() if s.name and s["st_info"]["type"] == "STT_FUNC"}
    return funcs - {"Reset_Handler", "Default_Handler", "Trap_Handler"}, ""


def classify(expect, got):
    if got[0] != "ok":
        return None
    if expect is None:
        return "value" if got[1] is None else None
    ety, ev = expect
    if isinstance(ev, str):
        return "nan-class" if nan_match(ety, ev, got[1]) else None
    mask = M32 if ety in ("i32", "f32") else M64
    return "value" if got[1] == (ev & mask) else None


def fmt(got):
    if got[0] == "ok":
        return "ok:" + ("-" if got[1] is None else f"0x{got[1]:x}")
    return ":".join(str(x) for x in got)


# ---------------------------------------------------------------------------
# One file, one leg
# ---------------------------------------------------------------------------
class FileRun:
    def __init__(self, leg, file):
        self.leg, self.file = leg, file
        self.outcomes: dict = {}         # line -> (outcome, func, detail)
        self.emulations = 0
        self.harness_errors: list = []
        # Bare `invoke` actions are not directives in scope, but a declined one
        # is what puts the module state behind the script (`state-skew`), so
        # they are tallied too — never a silent drop.
        self.invokes: Counter = Counter()

    def put(self, line, outcome, func="", detail=""):
        assert line not in self.outcomes, f"{self.file}:{line} counted twice"
        self.outcomes[line] = (outcome, func, detail)


def group_modules(forms):
    """[(module_line, module_text | None, [(line, head, form_text)])] in file
    order. Directives before the first module are grouped under None."""
    groups = [[None, None, []]]
    for line, form in forms:
        h = head_of(form)
        if h == "module":
            groups.append([line, form, []])
        else:
            groups[-1][2].append((line, h, form))
    return groups


def run_group(engine, leg, fr: FileRun, mline, mtext, items, bits, tmp: Path):
    _target, _flags, dp, fpu, checked = LEGS[leg]
    scoped = [(ln, h, f) for ln, h, f in items if h in IN_SCOPE]

    def decline_all(reason):
        for ln, _, _ in scoped:
            fr.put(ln, f"notrep:{reason}")

    if mtext is None:
        decline_all("no-module")
        return
    try:
        sexp = parse_sexp(mtext)
    except Exception:
        # #197's minimal reader cannot read this module text (annotations.wast /
        # id.wast exotic identifiers). Counted, never a silent drop.
        decline_all("reader-unparseable")
        return
    if len(sexp) > 1 and isinstance(sexp[1], str) and sexp[1] in ("binary", "quote", "definition", "instance"):
        decline_all(f"module-form:{sexp[1]}")
        return
    if len(sexp) > 2 and isinstance(sexp[1], str) and sexp[1].startswith("$") \
            and isinstance(sexp[2], str) and sexp[2] in ("binary", "quote", "definition", "instance"):
        decline_all(f"module-form:{sexp[2]}")
        return
    kinds = [f[0] for f in sexp[1:] if isinstance(f, list) and f]
    if "import" in kinds or any(isinstance(f, list) and any(isinstance(x, list) and x and x[0] == "import"
                                                            for x in f) for f in sexp[1:]):
        decline_all("imports")
        return
    src = tmp / f"m{mline[0]}_{mline[1]}.wat"
    src.write_text(mtext)
    out = tmp / f"m{mline[0]}_{mline[1]}_{leg}.elf"
    funcs, err = compile_image(src, out, leg)
    if err.startswith("PANIC"):
        fr.harness_errors.append(f"{fr.file}:{mline} synth PANIC")
    if funcs is None:
        decline_all("module-declined")
        return
    try:
        store = wasmtime.Store(engine)
        ref = wasmtime.Instance(store, wasmtime.Module(engine, mtext), [])
        rex = ref.exports(store)
    except Exception:
        decline_all("wasmtime-instantiate")
        return
    try:
        img = Image(out, fpu)
        fr.emulations += 1
    except (UcError, RuntimeError, StopIteration, struct.error) as e:
        decline_all("boot-fault")
        fr.harness_errors.append(f"{fr.file}:{mline} boot: {e}")
        return
    rng = random.Random(zlib.crc32(f"{leg}|{fr.file}|{mline[0]}".encode()))
    after_envelope = False
    for line, kind, form in items:
        scoped_kind = kind in IN_SCOPE
        if kind not in IN_SCOPE + ("invoke",):
            continue  # register / assert_invalid / assert_malformed / ...: no action
        try:
            try:
                act = parse_sexp(form)
            except Exception:
                raise Decl("unparseable")
            action = act if kind == "invoke" else (act[1] if len(act) > 1 else None)
            if not isinstance(action, list) or not action:
                raise Decl("no-action")
            if action[0] == "get":
                raise Decl("get-action")
            if action[0] == "module":
                raise Decl("module-trap")
            if action[0] != "invoke":
                raise Decl(f"action:{action[0]}")
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
            if fn not in funcs:
                raise Decl("symbol-missing")
            if not fpu and any(t in ("f32", "f64") for t in results):
                raise Decl("float-on-soft-target")
            if not dp and "f64" in results:
                raise Decl("f64-on-sp-target")
            core, sregs = marshal(args, dp, fpu)
        except Decl as e:
            if scoped_kind:
                fr.put(line, f"notrep:{e.reason}")
            else:
                fr.invokes[f"declined:{e.reason}"] += 1
            continue
        involves_float = any(t in ("f32", "f64") for t in params + results)
        has_nan = any(t in ("f32", "f64") and is_nan(t, v) for t, v in args)
        try:
            r = f(store, *[to_py(t, v) for t, v in args])
            wref = ("ok", None if r is None else from_py(results[0], r))
        except wasmtime.Trap:
            wref = ("trap",)
        outs, mem_after = {}, {}
        if involves_float:
            snap = img.snapshot()
            res, viol = img.call(fn, core, sregs, results, False, rng)
            fr.emulations += 1
            outs["zeroed"] = (res, viol)
            mem_after["zeroed"] = img.memory()
            img.restore(snap)
        res, viol = img.call(fn, core, sregs, results, True, rng)
        fr.emulations += 1
        outs["garbage"] = (res, viol)
        if involves_float:  # two machine states to compare; one state needs no copy
            mem_after["garbage"] = img.memory()
        if not scoped_kind:
            fr.invokes["executed"] += 1
            continue
        detail = f"{fn}({','.join(f'{t}:0x{v:x}' for t, v in args)})"

        def failed(outcome, text):
            if after_envelope:
                fr.put(line, "notrep:after-envelope", fn, text)
            else:
                fr.put(line, outcome, fn, text)

        if kind == "assert_trap":
            msg = act[-1].text() if isinstance(act[-1], WastStr) else ""
            if wref[0] != "trap":
                fr.put(line, "notrep:state-skew", fn, detail + " wasmtime did not trap")
                continue
            if all(o[0][0] in ("trap", "fault") for o in outs.values()):
                fr.put(line, "pass:trap", fn)
                continue
            if "out of bounds memory access" in msg and not checked:
                fr.put(line, "notrep:envelope:oob-unchecked", fn, detail)
                after_envelope = True
                continue
            failed("fail:missing-trap", detail + f" expected trap '{msg}', got " +
                   " ".join(f"{k}={fmt(o[0])}" for k, o in outs.items()))
            continue
        if wref[0] == "trap":
            # wasmtime TRAPPED where the script expects a value: an action
            # declined on BOTH engines (a bare `invoke` of a function synth
            # skipped — bulk.wast's `table.copy`) left the state behind the
            # script. The image is held to wasmtime: trapping too is skew.
            if all(o[0][0] in ("trap", "fault") for o in outs.values()):
                fr.put(line, "notrep:state-skew", fn, detail + " wasmtime and image both trapped")
            else:
                failed("fail:wrong-vs-reference", detail + " wasmtime trapped, image " +
                       " ".join(f"{k}={fmt(o[0])}" for k, o in outs.items()))
            continue
        skew = False
        if wref[0] == "ok" and expect is not None and not isinstance(expect[1], str) \
                and not has_nan and not is_nan(expect[0], expect[1]) \
                and wref[1] is not None and not is_nan(expect[0], wref[1]) \
                and wref[1] != (expect[1] & (M32 if expect[0] in ("i32", "f32") else M64)):
            skew = True
            expect = (expect[0], wref[1])
        verdicts = {k: classify(expect, o[0]) for k, o in outs.items()}
        viols = sorted({v for o in outs.values() for v in o[1]})
        if viols:
            failed("fail:contract-violation", detail + " " + "; ".join(viols))
            continue
        if len(set(mem_after.values())) > 1:
            failed("fail:state-dependent-memory", detail)
            continue
        if all(v is not None for v in verdicts.values()):
            if skew:
                fr.put(line, "notrep:state-skew", fn, detail + " image == wasmtime != literal")
            else:
                v = "nan-class" if "nan-class" in verdicts.values() else "value"
                fr.put(line, f"pass:{v}", fn)
            continue
        bad = [k for k, v in verdicts.items() if v is None]
        want = "-" if expect is None else (expect[1] if isinstance(expect[1], str) else f"0x{expect[1]:x}")
        text = detail + f" [{'+'.join(bad)}] want {want} got " + " ".join(f"{k}={fmt(o[0])}" for k, o in outs.items())
        if skew:
            failed("fail:wrong-vs-reference", text)
        elif all(outs[k][0][0] == "ok" for k in bad):
            failed("fail:wrong-value", text)
        else:
            failed("fail:no-value", text)


def run_file(engine, leg, wast: Path, tmp: Path) -> FileRun:
    fr = FileRun(leg, wast.name)
    text = wast.read_text(errors="replace")
    forms = top_forms_at(text)
    groups = group_modules(forms)
    lits: set = set()
    for _, _, items in groups:
        for _, h, f in items:
            if h in IN_SCOPE + ("invoke",):
                try:
                    collect_literals(parse_sexp(f), lits)
                except Exception:
                    pass
    try:
        bits = literal_bits(engine, lits)
    except Exception as e:
        fr.harness_errors.append(f"{wast.name}: literal bits: {str(e)[:120]}")
        for _, _, items in groups:
            for ln, h, _ in items:
                if h in IN_SCOPE:
                    fr.put(ln, "notrep:harness-error")
        return fr
    with tempfile.TemporaryDirectory(dir=tmp) as td:
        for mline, mtext, items in groups:
            done = set(fr.outcomes)
            try:
                run_group(engine, leg, fr, mline, mtext, items, bits, Path(td))
            except Exception as e:
                fr.harness_errors.append(f"{wast.name}:{mline}: {type(e).__name__}: {str(e)[:120]}")
                for ln, h, _ in items:
                    if h in IN_SCOPE and ln not in fr.outcomes and ln not in done:
                        fr.put(ln, "notrep:harness-error")
    return fr


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", help="substring filter on file name (floors not applied)")
    ap.add_argument("--leg", action="append", choices=sorted(LEGS))
    ap.add_argument("--suite-dir", default=str(SUITE_DIR), help="corpus directory (controls)")
    ap.add_argument("--json", help="write the per-directive ledger here")
    ap.add_argument("--emit-baseline", action="store_true", help="print the KNOWN literal for the failures seen")
    args = ap.parse_args()
    legs = tuple(args.leg or LEGS)
    suite = Path(args.suite_dir)
    full = not (args.only or args.leg)

    files = sorted(suite.glob("*.wast"))
    fails = []
    if len(files) != SUITE_FILES:
        fails.append(f"CORPUS: {len(files)} .wast files in {suite}, pinned {SUITE_FILES} "
                     f"(an empty checkout needs `submodules: recursive`)")
    if args.only:
        files = [f for f in files if args.only in f.name]
    if not files:
        print("FAIL: no corpus files")
        for f in fails:
            print(f"FAIL: {f}")
        return 1
    if not Path(SYNTH).is_file():
        print(f"FAIL: synth not found at {SYNTH}")
        return 1

    # The denominator — before anything executes.
    census = {f.name: directive_census(f.read_text(errors="replace")) for f in files}
    positions = {f.name: directive_positions(f.read_text(errors="replace")) for f in files}
    invokes = defaultdict(Counter)
    total = sum(sum(c.values()) for c in census.values())
    if full and total != DIRECTIVES_TOTAL:
        fails.append(f"CORPUS: {total} in-scope directives, pinned {DIRECTIVES_TOTAL}")
    if SYNTH_TEST:
        disagree, unparsed = [], []
        for f in files:
            n = synth_test_counts(f)
            if n is None:
                unparsed.append(f.name)
            elif n != census[f.name]["assert_return"]:
                disagree.append(f"{f.name}: synth-test {n} != {census[f.name]['assert_return']}")
        print(f"  second parser (synth-test stats): {len(files) - len(unparsed) - len(disagree)} files agree, "
              f"{len(disagree)} disagree, {len(unparsed)} not parsed by it ({', '.join(unparsed) or '-'})")
        fails.extend(f"PARSER DISAGREEMENT: {d}" for d in disagree)

    engine = wasmtime.Engine()
    runs: list = []
    t0 = time.monotonic()
    with tempfile.TemporaryDirectory() as td:
        for leg in legs:
            for f in files:
                runs.append(run_file(engine, leg, f, Path(td)))
    secs = time.monotonic() - t0

    by_leg = defaultdict(Counter)
    actual = {}
    ledger = []
    for fr in runs:
        c = Counter(o for o, _, _ in fr.outcomes.values())
        by_leg[fr.leg].update(c)
        want = sum(census[fr.file].values())
        if len(fr.outcomes) != want:
            fails.append(f"ACCOUNTING: {fr.leg} {fr.file}: {len(fr.outcomes)} directives accounted, "
                         f"{want} in the file")
        elif set(fr.outcomes) != positions[fr.file]:
            fails.append(f"ACCOUNTING: {fr.leg} {fr.file}: accounted positions differ from the census "
                         f"({sorted(set(fr.outcomes) ^ positions[fr.file])[:4]})")
        invokes[fr.leg].update(fr.invokes)
        for (line, col), (o, fn, d) in sorted(fr.outcomes.items()):
            ledger.append(dict(leg=fr.leg, file=fr.file, line=line, col=col, outcome=o, func=fn, detail=d))
            if o.startswith("fail:"):
                actual[(fr.leg, fr.file, line, col)] = (o, fn, d)
        for h in fr.harness_errors:
            fails.append(f"HARNESS ERROR: {fr.leg} {h}")

    print(f"#1636 spec-suite execution — {len(files)} files, {total} in-scope directives "
          f"(assert_return + assert_trap), legs {','.join(legs)}, {secs:.0f}s")
    for leg in legs:
        c = by_leg[leg]
        p = sum(v for k, v in c.items() if k.startswith("pass:"))
        fl = sum(v for k, v in c.items() if k.startswith("fail:"))
        nr = sum(v for k, v in c.items() if k.startswith("notrep:"))
        print(f"  [{leg}] executed {p + fl} = pass {p} + fail {fl}; not-representable {nr}; "
              f"sum {p + fl + nr} of {total}")
        print("     pass:   " + ", ".join(f"{k[5:]}={v}" for k, v in sorted(c.items()) if k.startswith("pass:")))
        print("     fail:   " + (", ".join(f"{k[5:]}={v}" for k, v in sorted(c.items()) if k.startswith("fail:"))
                                 or "none"))
        print("     notrep: " + ", ".join(f"{k[7:]}={v}" for k, v in sorted(c.items(), key=lambda kv: -kv[1])
                                         if k.startswith("notrep:")))
        print("     bare invokes (state only, not graded): " +
              ", ".join(f"{k}={v}" for k, v in sorted(invokes[leg].items(), key=lambda kv: -kv[1])))
        if full and p + fl < EXECUTED_FLOOR[leg]:
            fails.append(f"NON-VACUITY: {leg} executed {p + fl} < floor {EXECUTED_FLOOR[leg]}")
        if p + fl == 0 and total:
            fails.append(f"NON-VACUITY: {leg} executed 0 directives")

    if args.json:
        Path(args.json).write_text(json.dumps(dict(by_leg=by_leg, ledger=ledger), indent=1))
    if args.emit_baseline:
        print("KNOWN = {")
        for (leg, file, line, col), (o, fn, d) in sorted(actual.items()):
            print(f"    ({leg!r}, {file!r}, {line}, {col}, {o!r}): 'TODO',  # {fn}: {d[:100]}")
        print("}")

    ran = {(fr.leg, fr.file) for fr in runs}
    known_pos = {k[:4]: k[4] for k in KNOWN}
    for pos, (o, fn, d) in sorted(actual.items()):
        if pos + (o,) in KNOWN:
            continue
        if pos in known_pos:
            fails.append(f"BASELINE ENTRY MOVED: {pos} {fn} now {o}, baseline {known_pos[pos]} "
                         f"({KNOWN[pos + (known_pos[pos],)]}) {d[:120]}")
        else:
            fails.append(f"NEW FAILURE (not in baseline): {pos} {o} {d[:160]}")
    for key, reason in sorted(KNOWN.items()):
        pos = key[:4]
        if (key[0], key[1]) in ran and pos not in actual:
            got = next((r.outcomes.get((key[2], key[3])) for r in runs if (r.leg, r.file) == key[:2]), None)
            fails.append(f"BASELINE ENTRY NOW PASSES: {key} ({reason}) is now "
                         f"{got[0] if got else 'absent'} — remove it in the same PR")
    nfail = len(actual)
    print(f"  baseline: {len(KNOWN)} entries; failures this run {nfail}, "
          f"in baseline {sum(1 for p, v in actual.items() if p + (v[0],) in KNOWN)}")
    executed = sum(sum(v for k, v in by_leg[leg].items() if not k.startswith("notrep:")) for leg in legs)
    print(f"#1636 EXECUTED={executed} directives across {len(legs)} legs")
    if fails:
        for f in fails[:80]:
            print(f"FAIL: {f}")
        if len(fails) > 80:
            print(f"FAIL: ... and {len(fails) - 80} more")
        return 1
    print("RESULT: PASS — every executed directive matches the spec's expected result or is an exact "
          "baseline entry, and every directive is accounted for")
    return 0


if __name__ == "__main__":
    sys.exit(main())
