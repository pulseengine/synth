#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 5715
"""RQ-91-ARMV6M (#1301) — the cortex-m0 / cortex-m0plus profile, SUPPORT LEVEL 3.

WHAT EXISTS. `--target cortex-m0` and `--target cortex-m0plus` (ARMv6-M,
triple thumbv6m-none-eabi, no FPU), on ONE shape: an ARM `--relocatable`
object. synth has NO ARMv6-M lowering — the selector and encoder are the
ARMv7-M ones — so every encoded instruction goes through the ARMv6-M byte
check (`crates/synth-backend/src/armv6m.rs`) and a function containing
anything outside ARMv6-M is REFUSED, loudly, naming the offset and the class.
The claim is exactly: what compiles on the profile is ARMv6-M (static), and
computes what wasmtime computes ON AN ARMv6-M CPU MODEL (execution). Nothing
more.

RED BEFORE: on main 6b697bcf both targets exit 1 ("unknown target triple").
Leg A fails there.

THE LEGS
  A  profile + loud declines. The fixture compiles with BOTH targets to the
     SAME .text; the accepted set is EXACTLY `ACCEPTED`, and every other
     export declines with EXACTLY the class in `EXPECTED_DECLINES` (pinned
     both directions). Self-contained images and `-b riscv` are refused.
  B  static, over the WHOLE .text of every accepted object — not just the
     encode loop's view, so code emitted anywhere else is covered too: every
     instruction is in the frozen LLVM-derived 16-bit table
     (tests/fixtures/armv6m_legal16_1301.json) or is BL / DMB / DSB / ISB SY;
     no 16-bit LDR (literal) (the compiler refuses it too; this is the second
     check) and no pool words; every STT_FUNC symbol has the
     Thumb bit. A PLANTED v7-M MOVW, IT and CBZ in a copy must each turn this
     leg RED. Leg B is the ONLY guard against IT and CBZ/CBNZ: the unicorn M0
     model below EXECUTES them (see THE CPU MODEL).
  C  execution: every accepted function whose parameters fit R0-R3 (i32 and
     i64, AAPCS even-pair alignment) and whose result is none, i32 or i64 —
     from the fixture AND from every tracked .wat/.wasm in this repo — runs on
     unicorn's Cortex-M0 model on a vector set and must equal wasmtime.
  D  model potency, every run. A cortex-m3 object whose .text carries a v7-M
     `and.w` (the `i32_and` probe) is executed by the SAME harness as leg C:
     on the M0 model it MUST fault as an ILLEGAL INSTRUCTION at the `and.w`;
     on the M3 model (control) the same bytes MUST return wasmtime's value.
     Plus the classifier on synthetic bytes: `udf #0` is a TRAP, `and.w` and
     the 16-bit undefined halfword 0xB800 are ILLEGAL; and the comparator
     (`verdict()`) on every (wasmtime outcome, unicorn outcome) pair. If the
     model were not set, or set too late, or the classifier counted any other
     invalid instruction (32- or 16-bit) as a trap, or the comparator let an
     illegal, fault or hang stand for a wasm trap or a budget pass, this leg
     reds.
  E  per-op probes (`PROBES`, 112 single-export modules, embedded here so they
     move no corpus-derived pin). Each compiles for cortex-m0, cortex-m0plus
     and cortex-m3. The v6-M accepted set is EXACTLY `PROBE_ACCEPTED` on both
     targets (both directions); cortex-m3 accepts every probe but
     `PROBE_M3_DECLINED` (the control: a probe that does not compile on v7-M
     says nothing about v6-M). Each accepted probe's v6-M .text is identical
     on both targets, passes leg B, and executes as leg C.
  V  the value comparison's red half. Real cortex-m0 bytes from leg E against
     a DELIBERATELY WRONG wasmtime reference under the same export name (a
     wrong operation, an off-by-one result, an i64 reference with the high
     word dropped) must disagree on exactly the vectors where the two
     functions differ, computed independently. Run on the M0 model, recorded
     under its own leg, so no real pin or count sees it.
  BINDING. `execute()` takes the CPU model and the leg as REQUIRED arguments,
     records the model the live `Uc` reads back under that leg, and the run
     reds unless legs C, E and V ran on the M0 model and nothing else. It also
     counts VALUE COMPARISONS (wasmtime and unicorn both returned a value) for
     legs C and E and holds them to `VALUE_COMPARISONS_FLOOR`, printed as
     `#1301 M0ORACLE VALUE-COMPARISONS=N` — the header's emulation floor
     counts emulator entries, which a comparator that ignored the value would
     still produce. The comparison rule itself lives in `verdict()`, and leg D
     checks it on every outcome kind. Every vector of legs C and E lands in
     exactly one bucket (compared, trap, void, budget, disagree) and the
     buckets must sum to the vectors run, so no pass goes uncounted.

THE CPU MODEL. unicorn is constructed as `Uc(UC_ARCH_ARM, UC_MODE_THUMB)` with
`ctl_set_cpu_model(UC_CPU_ARM_CORTEX_M0)` BEFORE the first `mem_map`, and the
model is READ BACK and asserted equal; any other value aborts the run. With
that construction unicorn 2.1.4 enforces ARMv6-M for the 32-bit space (MOVW,
SDIV/UDIV, `and.w`, `ldr.w`, `push.w`, UMULL, MLS, CLZ, RBIT, LDRD, TBB all
fault; in a 30,000-word sample the only 32-bit words that run and fail the
repo's predicate are MSR forms, which are ARMv6-M). Two constructions do NOT
enforce it, which is where the earlier "the model is inert" reading came
from: `UC_MODE_THUMB | UC_MODE_MCLASS` reads back 11 (M33) whatever was set,
and setting the model after `mem_map` returns UC_ERR_ARG. The model is a
property of the unicorn VERSION, so the version is pinned (`UNICORN_VERSION`,
and `unicorn==2.1.4` in the CI install step) and asserted here.

What the M0 model does NOT enforce: it EXECUTES all 1,024 CBZ/CBNZ and all
240 IT halfwords (IT as a real IT block, not a hint) — 1,266 of the 2,210
halfwords the frozen table calls illegal. Those are leg B's to catch, and leg
B's planted IT and CBZ controls prove it does.

A TRAP IS A UDF. Under the M0 model a wasm trap (`udf #0`, 0xDE00-0xDEFF) and a
v7-M instruction raise the SAME error, UC_ERR_INSN_INVALID, with PC at the
faulting instruction. So a fault counts as a wasm trap ONLY when the halfword
at the faulting PC is a 16-bit UDF; any other invalid-instruction fault is an
ILLEGAL-INSTRUCTION failure whatever wasmtime did, and any other unicorn error
(memory, exception) or a run that does not return is a failure too. The one
exception is a vector on which wasmtime itself runs out of FUEL (a loop
counting down from a large argument): there is no reference value and no wasm
trap, so the vector is a BUDGET outcome — counted and printed, never counted as
agreement, and failed unless unicorn ALSO ran out of its own instruction budget:
a return, an illegal instruction, a fault or a trap there is a failure (RQ-91-
M0I32, cold review 15 F5: a budget vector used to pass whatever unicorn
returned). The budget vectors are pinned EXACTLY, per function, in
`BUDGET_EXPECTED`, so a new argument-counted loop cannot join unseen. (Before
v0.91 M0ORACLE any unicorn stop was compared equal to any wasmtime exception,
so these five vectors of `join_alias_1189.wat:lres` passed as "both trapped".)
A `Uc`
that faulted at an address keeps faulting there after the bytes are rewritten,
so every potency control builds a FRESH `Uc`.

CORTEX-M0+ RUNS ON THE M0 MODEL. unicorn has no Cortex-M0+ CPU model (no
`UC_CPU_ARM_CORTEX_M0PLUS` constant in 2.1.4; this script reds if one appears,
so the choice gets revisited). That is acceptable HERE, for two reasons that
are both checked rather than assumed: M0 and M0+ implement the same
instruction set, ARMv6-M (the M0+ differences are the 2-stage pipeline, the
single-cycle I/O port, the optional MPU and VTOR — timing and system level,
none of which a register-in/register-out differential observes); and leg A /
leg E assert the cortex-m0plus .text is byte-identical to the cortex-m0 .text,
so the bytes executed ARE the cortex-m0plus bytes. It would stop being
acceptable the day the two targets emit different code, which is exactly when
the identity assertion reds.

Run:  SYNTH=target/debug/synth python3 scripts/repro/armv6m_1301_differential.py
"""
import collections
import hashlib
import json
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import unicorn
import unicorn.arm_const as arm_const
import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_ERR_INSN_INVALID, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1,
                               UC_ARM_REG_SP, UC_CPU_ARM_CORTEX_M0, UC_CPU_ARM_CORTEX_M3)

ROOT = Path(__file__).resolve().parents[2]
SYNTH = os.environ.get("SYNTH", str(ROOT / "target/debug/synth"))
WAT = Path(__file__).with_name("armv6m_1301.wat")
FIXTURE = ROOT / "tests/fixtures/armv6m_legal16_1301.json"
TARGETS = ("cortex-m0", "cortex-m0plus")
BASE = ["--relocatable", "--all-exports", "--allow-skipped-exports"]
EMBED = ["--embedder-data-init", "--embedder-global-init"]

# The CPU model's behaviour is a property of the unicorn release; the CI step
# installs exactly this one.
UNICORN_VERSION = "2.1.4"
M0_MODEL = UC_CPU_ARM_CORTEX_M0  # 7 in 2.1.4
M3_MODEL = UC_CPU_ARM_CORTEX_M3  # 8 in 2.1.4, leg D's control only

ACCEPTED = {"inc", "sub3", "ext8", "big", "lt", "bits", "mul"}
# Each refused export -> the class its FIRST non-ARMv6-M instruction hits.
# RQ-91-M0I32: the three still refused are refused by the v6-M lowering's rule
# table before any byte is encoded; its diagnostic carries no byte class, so
# each pin is the diagnostic's own prefix.
_LOWERING = "backend 'arm' failed: compilation failed: ARMv6-M lowering, RQ-91-M0I32"
EXPECTED_DECLINES = {
    "divu": f"warning: skipping function 'divu': {_LOWERING}",
    "callinc": f"warning: skipping function 'callinc': {_LOWERING}",
    "ld": f"warning: skipping function 'ld': {_LOWERING}",
}

LEGAL = [tuple(r) for r in json.loads(FIXTURE.read_text())["legal_ranges"]]
FAILS = []


def fail(msg):
    FAILS.append(msg)
    print("FAIL", msg)


def abort(msg):
    """The harness itself is not what it claims to be: no verdict is possible."""
    print(f"ABORT {msg}")
    print("ORACLE: FAIL (harness abort)")
    sys.exit(2)


# ---- leg E: the per-op probes ----------------------------------------------
# One export per wasm op or shape, each its own module (a probe's acceptance
# must not depend on its neighbours). Transcribed from the v0.91 M0 plan's
# probe_ops.py, 2026-11-18, synth main 265235dc: 112 probes, 8 accepted on
# both ARMv6-M targets, 110 on cortex-m3.
def _b1(op, t="i32"):
    return f"(param {t}) (result {t}) ({t}.{op} (local.get 0))"


def _b2(op, t="i32", r=None):
    return f"(param {t} {t}) (result {r or t}) ({t}.{op} (local.get 0) (local.get 1))"


def _probes():
    p = collections.OrderedDict()

    def add(name, body):
        assert body.count("(") == body.count(")"), name
        assert name not in p, name
        p[name] = body

    add("c_small", "(result i32) (i32.const 42)")
    add("c_255", "(result i32) (i32.const 255)")
    add("c_256", "(result i32) (i32.const 256)")
    add("c_ffff", "(result i32) (i32.const 65535)")
    add("c_big", "(result i32) (i32.const 0x12345678)")
    add("c_neg1", "(result i32) (i32.const -1)")
    add("add_imm1", "(param i32) (result i32) (i32.add (local.get 0) (i32.const 1))")
    add("add_imm200", "(param i32) (result i32) (i32.add (local.get 0) (i32.const 200))")
    add("add_imm1000", "(param i32) (result i32) (i32.add (local.get 0) (i32.const 1000))")
    for op in ("add", "sub", "mul", "and", "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr",
               "div_s", "div_u", "rem_s", "rem_u"):
        add("i32_" + op, _b2(op))
    add("shl_imm3", "(param i32) (result i32) (i32.shl (local.get 0) (i32.const 3))")
    for op in ("clz", "ctz", "popcnt", "extend8_s", "extend16_s"):
        add("i32_" + op, _b1(op))
    add("i32_eqz", "(param i32) (result i32) (i32.eqz (local.get 0))")
    for op in ("eq", "ne", "lt_s", "lt_u", "gt_s", "gt_u", "le_s", "le_u", "ge_s", "ge_u"):
        add("i32_" + op, _b2(op))
    add("select", "(param i32 i32 i32) (result i32) "
        "(select (local.get 0) (local.get 1) (local.get 2))")
    add("if_else", "(param i32) (result i32) "
        "(if (result i32) (local.get 0) (then (i32.const 1)) (else (i32.const 2)))")
    add("if_void", "(param i32) (result i32) (local i32) "
        "(if (local.get 0) (then (local.set 1 (i32.const 5)))) (local.get 1)")
    add("block_br_if", "(param i32) (result i32) "
        "(block (result i32) (i32.const 7) (br_if 0 (local.get 0)) (drop) (i32.const 9))")
    add("loop_count", "(param i32) (result i32) (local i32) (block (loop "
        "(br_if 1 (i32.eqz (local.get 0))) "
        "(local.set 1 (i32.add (local.get 1) (local.get 0))) "
        "(local.set 0 (i32.sub (local.get 0) (i32.const 1))) (br 0))) (local.get 1)")
    add("br_table", "(param i32) (result i32) (block (block (block "
        "(br_table 0 1 2 (local.get 0))) (return (i32.const 10))) "
        "(return (i32.const 20))) (i32.const 30)")
    add("early_return", "(param i32) (result i32) "
        "(if (local.get 0) (then (return (i32.const 1)))) (i32.const 0)")
    add("unreachable", "(param i32) (result i32) "
        "(if (local.get 0) (then (unreachable))) (i32.const 0)")
    add("nop_drop", "(param i32) (result i32) (nop) (drop (i32.const 1)) (local.get 0)")
    add("local_tee", "(param i32) (result i32) (local i32) "
        "(i32.add (local.tee 1 (local.get 0)) (local.get 1))")
    add("many_locals", "(param i32) (result i32) (local i32 i32 i32 i32 i32 i32 i32 i32) "
        + " ".join(f"(local.set {i} (i32.add (local.get {i - 1}) (i32.const {i})))"
                   for i in range(1, 9))
        + " (i32.add (i32.add (i32.add (local.get 1) (local.get 2)) "
          "(i32.add (local.get 3) (local.get 4))) (i32.add (i32.add (local.get 5) "
          "(local.get 6)) (i32.add (local.get 7) (local.get 8))))")
    add("params5", "(param i32 i32 i32 i32 i32) (result i32) "
        "(i32.add (local.get 0) (local.get 4))")
    add("void_fn", "(param i32)")
    add("call_direct", "(param i32) (result i32) (call $callee (local.get 0))")
    add("call_import", "(param i32) (result i32) (call $imp (local.get 0))")
    add("call_indirect", "(param i32) (result i32) "
        "(call_indirect (type $t1) (local.get 0) (i32.const 0))")
    for op in ("load", "load8_u", "load8_s", "load16_u", "load16_s"):
        add("i32_" + op, f"(param i32) (result i32) (i32.{op} (local.get 0))")
    add("i32_load_off", "(param i32) (result i32) (i32.load offset=16 (local.get 0))")
    add("i32_load_const", "(result i32) (i32.load (i32.const 64))")
    for op in ("store", "store8", "store16"):
        add("i32_" + op, f"(param i32 i32) (i32.{op} (local.get 0) (local.get 1))")
    add("memory_size", "(result i32) (memory.size)")
    add("memory_grow", "(param i32) (result i32) (memory.grow (local.get 0))")
    add("memory_fill", "(param i32 i32 i32) "
        "(memory.fill (local.get 0) (local.get 1) (local.get 2))")
    add("memory_copy", "(param i32 i32 i32) "
        "(memory.copy (local.get 0) (local.get 1) (local.get 2))")
    add("global_get", "(result i32) (global.get $g)")
    add("global_set", "(param i32) (global.set $g (local.get 0))")
    add("i64_const", "(result i64) (i64.const 0x1122334455667788)")
    add("i64_const_small", "(result i64) (i64.const 5)")
    add("i64_ident", "(param i64) (result i64) (local.get 0)")
    for op in ("add", "sub", "mul", "and", "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr",
               "div_s", "div_u", "rem_s", "rem_u"):
        add("i64_" + op, _b2(op, "i64"))
    for op in ("clz", "ctz", "popcnt", "extend8_s", "extend16_s", "extend32_s"):
        add("i64_" + op, _b1(op, "i64"))
    add("i64_eqz", "(param i64) (result i32) (i64.eqz (local.get 0))")
    for op in ("eq", "ne", "lt_s", "lt_u", "ge_s", "ge_u"):
        add("i64_" + op, _b2(op, "i64", "i32"))
    add("i64_extend_i32_s", "(param i32) (result i64) (i64.extend_i32_s (local.get 0))")
    add("i64_extend_i32_u", "(param i32) (result i64) (i64.extend_i32_u (local.get 0))")
    add("i32_wrap_i64", "(param i64) (result i32) (i32.wrap_i64 (local.get 0))")
    add("i64_select", "(param i64 i64 i32) (result i64) "
        "(select (local.get 0) (local.get 1) (local.get 2))")
    add("i64_load", "(param i32) (result i64) (i64.load (local.get 0))")
    add("i64_store", "(param i32 i64) (i64.store (local.get 0) (local.get 1))")
    add("f32_add", "(param f32 f32) (result f32) (f32.add (local.get 0) (local.get 1))")
    add("f64_add", "(param f64 f64) (result f64) (f64.add (local.get 0) (local.get 1))")
    return p


PROBES = _probes()
PROBE_COUNT = 112
# EXACT, both directions, on cortex-m0 AND cortex-m0plus. A lowering lane that
# makes a probe compile moves this set in its own PR.
# RQ-91-M0I32: 8 -> 51 (the ARMv6-M i32 lowering).
PROBE_ACCEPTED = {"add_imm1", "add_imm1000", "add_imm200", "block_br_if", "br_table",
                  "c_255", "c_256", "c_big", "c_ffff", "c_neg1", "c_small",
                  "early_return", "i32_add", "i32_and", "i32_eq", "i32_eqz",
                  "i32_extend16_s", "i32_extend8_s", "i32_ge_s", "i32_ge_u",
                  "i32_gt_s", "i32_gt_u", "i32_le_s", "i32_le_u", "i32_lt_s",
                  "i32_lt_u", "i32_mul", "i32_ne", "i32_or", "i32_rotl", "i32_rotr",
                  "i32_shl", "i32_shr_s", "i32_shr_u", "i32_sub", "i32_xor", "i64_and",
                  "i64_extend_i32_u", "i64_ident", "i64_or", "i64_xor", "if_else",
                  "if_void", "local_tee", "loop_count", "many_locals", "nop_drop",
                  "select", "shl_imm3", "unreachable", "void_fn"}
# The control: cortex-m3 compiles every probe but these (no FPU on m3).
PROBE_M3_DECLINED = {"f32_add", "f64_add"}
# Leg D's v7-M-only carrier, compiled for cortex-m3.
POTENCY_PROBE = "i32_and"


def probe_module(name, body):
    pre = ""
    if name == "call_direct":
        pre = "(func $callee (param i32) (result i32) (i32.add (local.get 0) (i32.const 1)))"
    elif name == "call_import":
        pre = '(import "env" "imp" (func $imp (param i32) (result i32)))'
    elif name == "call_indirect":
        pre = ("(type $t1 (func (param i32) (result i32))) (table 2 funcref) "
               "(func $callee (param i32) (result i32) (local.get 0)) (elem (i32.const 0) $callee)")
    elif "global" in name:
        pre = "(global $g (mut i32) (i32.const 3))"
    mem = "(memory 1)" if ("load" in name or "store" in name or "memory" in name) else ""
    return f'(module {pre} {mem} (func (export "{name}") {body}))\n'


# ---- unicorn: the M0 model, constructed and checked ------------------------
def check_unicorn():
    if unicorn.__version__ != UNICORN_VERSION:
        abort(f"unicorn {unicorn.__version__} != pinned {UNICORN_VERSION}: the M0 model's "
              "enforcement is a property of the release; re-measure before re-pinning")
    if hasattr(arm_const, "UC_CPU_ARM_CORTEX_M0PLUS"):
        abort("unicorn now has a Cortex-M0+ model: run cortex-m0plus on it and revise "
              "the M0+ note in this script's docstring")


def make_uc(model):
    """Plain Thumb mode, model set BEFORE the first mem_map, readback asserted."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.ctl_set_cpu_model(model)
    got = mu.ctl_get_cpu_model()
    if got != model:
        abort(f"unicorn CPU model reads back {got}, set {model}: this Uc is not the "
              "CPU it claims to be (UC_MODE_MCLASS pins 11; a late set is refused)")
    return mu


def is_prefix(h):
    return (h >> 11) in (0b11101, 0b11110, 0b11111)


def legal16(h):
    return any(lo <= h <= hi for lo, hi in LEGAL)


def legal32(a, b):
    return (a >> 11 == 0b11110 and b & 0xD000 == 0xD000) or (
        a == 0xF3BF and b in (0x8F4F, 0x8F5F, 0x8F6F))


def is_udf16(h):
    return 0xDE00 <= h <= 0xDEFF


def scan_text(text):
    """First non-ARMv6-M instruction in `text` as (offset, hex), else None."""
    i = 0
    while i + 1 < len(text):
        h = struct.unpack_from("<H", text, i)[0]
        if is_prefix(h):
            if i + 3 >= len(text):
                return i, f"{h:04x} (truncated)"
            h2 = struct.unpack_from("<H", text, i + 2)[0]
            if not legal32(h, h2):
                return i, f"{h:04x} {h2:04x}"
            i += 4
        else:
            # 0x4800-0x4FFF is LDR (literal) T1: legal ARMv6-M, but the
            # compiler's check refuses it (no pool reach — 1020 B on v6-M — is
            # checked for this profile). This is the SECOND check of that rule,
            # over the whole .text, so a literal load emitted anywhere shows.
            if not legal16(h) or 0x4800 <= h <= 0x4FFF:
                return i, f"{h:04x}"
            i += 2
    return None


def load(path):
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        sec = e.get_section_by_name(".text")
        text = sec.data() if sec else b""
        syms, funcs = {}, []
        for s in e.get_section_by_name(".symtab").iter_symbols():
            if s["st_info"]["type"] == "STT_FUNC":
                funcs.append((s.name, s["st_value"], s["st_size"]))
                if s["st_info"]["bind"] == "STB_GLOBAL":
                    syms[s.name] = (s["st_value"], s["st_size"])
        relocs = []
        for rs in e.iter_sections():
            if rs["sh_type"] in ("SHT_REL", "SHT_RELA") and rs.name.endswith(".text"):
                relocs += [r["r_offset"] for r in rs.iter_relocations()]
    return text, syms, funcs, relocs


def leg_b(path, label):
    text, _, funcs, _ = load(path)
    bad = scan_text(text)
    if bad:
        fail(f"B {label}: non-ARMv6-M instruction at .text+0x{bad[0]:x}: {bad[1]}")
    for name, val, _ in funcs:
        if not val & 1:
            fail(f"B {label}: STT_FUNC {name} has no Thumb bit (value 0x{val:x})")
    return text


def synth(args):
    return subprocess.run([SYNTH, "compile", *args], capture_output=True, text=True,
                          env={**os.environ, "RUST_LOG": "error"}, timeout=300)


# Vectors on which wasmtime exhausted FUEL (a loop counting down from a large
# argument). Budget outcomes, NOT traps: reported, never counted as agreement.
BUDGET = collections.Counter()
FUEL = 10_000_000
# EXACT, both directions (RQ-91-M0I32, cold review 15 F5; was a ceiling of 5,
# all `join_alias_1189.wat:lres`, then 106). Every entry is a loop whose trip
# count is an argument, on the large vectors: wasmtime runs out of fuel and
# unicorn out of instructions, so there is no reference. Keyed by the leg and
# the tracked source (leg C) or probe (leg E).
BUDGET_EXPECTED = {
    "C scripts__repro__a32_control_flow_1639.wat.o:dowhile": 2,
    "C scripts__repro__a32_control_flow_1639.wat.o:nest": 8,
    "C scripts__repro__a32_control_flow_1639.wat.o:optloop": 4,
    "C scripts__repro__a32_control_flow_1639.wat.o:sum": 4,
    "C scripts__repro__aarch64_brtable_blockvals_851.wat.o:loop_value": 4,
    "C scripts__repro__aarch64_brtable_blockvals_851.wat.o:nested_value_frames": 4,
    "C scripts__repro__aarch64_brtable_blockvals_851.wat.o:table_loop_default_back": 2,
    "C scripts__repro__aarch64_brtable_blockvals_851.wat.o:table_loop_target0_back": 2,
    "C scripts__repro__aarch64_ctrlflow_851.wat.o:count_sum": 1,
    "C scripts__repro__aarch64_ctrlflow_851.wat.o:countdown": 4,
    "C scripts__repro__aarch64_ctrlflow_851.wat.o:do_while_count": 5,
    "C scripts__repro__aarch64_ctrlflow_851.wat.o:isqrt_ceil": 1,
    "C scripts__repro__aarch64_param_homing_851.wat.o:cond_write_param_loop": 4,
    "C scripts__repro__aarch64_param_homing_851.wat.o:param_countdown_sum": 4,
    "C scripts__repro__brif_local_zeroinit_990.wat.o:guard_loop_acc": 4,
    "C scripts__repro__cond_write_param_970.wat.o:cw_loop": 4,
    "C scripts__repro__home_alias_class_1189_i32.wat.o:loopcnt": 4,
    "C scripts__repro__if_arm_dead_value_1691.wat.o:t_i32_loop_exit": 3,
    "C scripts__repro__join_alias_1189.wat.o:iloop": 5,
    "C scripts__repro__join_alias_1189.wat.o:lres": 5,
    "C scripts__repro__loop_param_bound_663.wat.o:sum_below": 1,
    "C scripts__repro__loop_param_bound_663.wat.o:sum_nested": 2,
    "C scripts__repro__loop_param_bound_663.wat.o:sum_stride": 1,
    "C scripts__repro__optloop_backedge_1206.wat.o:countdown": 2,
    "C scripts__repro__optloop_backedge_1206.wat.o:countdown_r7": 2,
    "C scripts__repro__optloop_backedge_1206.wat.o:down_const": 2,
    "C scripts__repro__optloop_backedge_1206.wat.o:down_param": 4,
    "C scripts__repro__optloop_backedge_1206.wat.o:up_from_zero": 4,
    "C scripts__repro__optloop_backedge_1206.wat.o:up_param": 4,
    "C scripts__repro__param_block_silent_1097_loop.wat.o:lpb": 2,
    "C scripts__repro__param_block_silent_1097_loop_lowered.wat.o:lp2": 2,
    "C scripts__repro__param_block_silent_1097_loop_lowered.wat.o:lpa": 2,
    "C scripts__repro__param_block_silent_1097_loop_lowered.wat.o:lpd": 2,
    "C scripts__repro__param_block_silent_1097_loop_lowered.wat.o:lpx": 2,
    "E loop_count.cortex-m0.o:loop_count": 4,
}
VECTORS = [0, 1, 2, 7, 0x7F, 0x80, 0xFF, 0x1234, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF,
           0xDEADBEEF]
CODE, STK = 0x10000, 0x200000


def s32(v):
    return v - (1 << 32) if v >= 1 << 31 else v


def s64(v):
    return v - (1 << 64) if v >= 1 << 63 else v


def run_one(mu, entry, ret, regs, rs):
    """One call. Returns ("ok", value) | ("trap", pc) | ("illegal", pc, hw) |
    ("fault", detail) | ("hang", pc). A fault is a TRAP only at a 16-bit UDF."""
    for j, a in enumerate(regs):
        mu.reg_write(UC_ARM_REG_R0 + j, a)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        mu.emu_start(entry | 1, ret, timeout=2_000_000, count=1_000_000)
    except UcError as e:
        pc = mu.reg_read(UC_ARM_REG_PC) & ~1
        try:
            hw = struct.unpack("<H", bytes(mu.mem_read(pc, 2)))[0]
        except UcError:
            return ("fault", f"{e} at 0x{pc:x} (unreadable)")
        if e.errno == UC_ERR_INSN_INVALID:
            return ("trap", pc) if is_udf16(hw) else ("illegal", pc, hw)
        return ("fault", f"{e} at 0x{pc:x}")
    pc = mu.reg_read(UC_ARM_REG_PC) & ~1
    if pc != ret:
        return ("hang", pc)
    if rs == ["i32"]:
        return ("ok", mu.reg_read(UC_ARM_REG_R0))
    if rs == ["i64"]:
        return ("ok", mu.reg_read(UC_ARM_REG_R0) | (mu.reg_read(UC_ARM_REG_R1) << 32))
    return ("ok", None)


def describe(r):
    if r[0] == "ok":
        return "-" if r[1] is None else hex(r[1])
    if r[0] == "trap":
        return f"trap(udf @0x{r[1]:x})"
    if r[0] == "illegal":
        return f"ILLEGAL-INSTRUCTION {r[2]:04x} @0x{r[1]:x}"
    if r[0] == "hang":
        return f"did not return (pc 0x{r[1]:x})"
    return f"FAULT {r[1]}"


def aapcs_regs(ps):
    """Core-register slot of each param (i64 on an even pair), or None if >R3."""
    slots, n = [], 0
    for p in ps:
        if p == "i32":
            slots.append(n)
            n += 1
        elif p == "i64":
            n += n & 1
            slots.append(n)
            n += 2
        else:
            return None
    return slots if n <= 4 else None


# What each leg ACTUALLY ran on, read back from the live Uc (not the argument),
# and how many result VALUES each leg compared. Legs C and E must have run on
# the M0 model only, and must have compared at least the floor below — the
# emulation floor in the header counts emulator ENTRIES, which a comparator
# that ignores the value would still produce.
EXEC_MODELS = collections.defaultdict(set)
COMPARED = collections.Counter()
VECTORS_RUN = collections.Counter()
OUTCOMES = collections.defaultdict(collections.Counter)
# Measured at v0.91 M0ORACLE: 666 (vectors of the value-returning functions of
# legs C and E where wasmtime returned and unicorn returned a value to compare;
# trap and budget vectors are not comparisons). A floor: adding a fixture
# cannot redden it.
# RQ-91-M0I32: 666 -> 5472 (C 4887, E 585), measured after cold review 15 F1
# (functions the base rung cannot select now decline on ARMv6-M).
VALUE_COMPARISONS_FLOOR = 5472


def vector_args(ps, slots, k):
    """Vector k for params `ps`: (core registers R0-R3, wasm arguments)."""
    regs, args = [0, 0, 0, 0], []
    for j, (p, slot) in enumerate(zip(ps, slots)):
        a = VECTORS[(k + j * 5) % len(VECTORS)]
        if p == "i64":
            hi = VECTORS[(k + j * 5 + 3) % len(VECTORS)]
            regs[slot], regs[slot + 1] = a, hi
            args.append(s64(a | (hi << 32)))
        else:
            regs[slot] = a
            args.append(s32(a))
    return regs, args


def verdict(trapped, budget, exp, got):
    """The comparison rule, in one place: "agree" | "budget" | "disagree".

    - wasmtime ran out of FUEL: no reference exists. "budget" only if unicorn
      ALSO hit its own budget; a return (with any value), an illegal
      instruction, a CPU fault or a UDF trap is "disagree".
    - wasmtime TRAPPED: "agree" only on a UDF trap. ILLEGAL, FAULT and HANG
      are "disagree" whatever wasmtime did.
    - otherwise: "agree" only on a return with the identical value (all 64
      bits for an i64 result)."""
    if budget:
        return "budget" if got[0] == "hang" else "disagree"
    if trapped:
        return "agree" if got[0] == "trap" else "disagree"
    return "agree" if got[0] == "ok" and got[1] == exp else "disagree"


def execute(path, wasm_bytes, model, leg, only=None):
    """Run every executable accepted function of `path` vs wasmtime on `model`.
    `model` and `leg` have NO default: every caller states the CPU it means,
    and the model the Uc reads back is recorded under `leg`.
    Returns (#functions run, [problem strings]); the caller decides."""
    text, syms, _, relocs = load(path)
    cfg = wasmtime.Config()
    cfg.consume_fuel = True
    eng = wasmtime.Engine(cfg)
    try:
        mod = wasmtime.Module(eng, wasm_bytes)
        store = wasmtime.Store(eng)
        store.set_fuel(10_000_000)
        inst = wasmtime.Instance(store, mod, [])
    except Exception:
        return 0, []  # imports / unsupported: not executable standalone
    exports = inst.exports(store)
    mu = make_uc(model)
    EXEC_MODELS[leg].add(mu.ctl_get_cpu_model())
    size = (len(text) + 0x1FFF) & ~0xFFF
    mu.mem_map(CODE, size + 0x1000)
    mu.mem_write(CODE, text)
    mu.mem_map(STK, 0x10000)
    ret = CODE + size
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    ran, problems = 0, []
    for name, (val, sz) in sorted(syms.items()):
        if only is not None and name not in only:
            continue
        f = exports.get(name) if hasattr(exports, "get") else None
        if f is None:
            try:
                f = exports[name]
            except Exception:
                continue
        if not isinstance(f, wasmtime.Func):
            continue
        ty = f.type(store)
        ps, rs = [str(p) for p in ty.params], [str(r) for r in ty.results]
        slots = aapcs_regs(ps)
        if slots is None or rs not in ([], ["i32"], ["i64"]):
            continue
        lo = val & ~1
        if any(lo <= r < lo + sz for r in relocs):
            continue  # calls something: needs a link step this leg does not do
        ran += 1
        for k in range(len(VECTORS)):
            regs, args = vector_args(ps, slots, k)
            budget = False
            try:
                store.set_fuel(FUEL)
                exp = f(store, *args)
                exp = None if exp is None else exp & ((1 << 64) - 1 if rs == ["i64"] else 0xFFFFFFFF)
                trapped = False
            except wasmtime.Trap as x:
                trapped, exp = True, None
                budget = x.trap_code == wasmtime.TrapCode.OUT_OF_FUEL
            except Exception:
                trapped, exp = True, None
            got = run_one(mu, CODE + lo, ret, regs, rs)
            v = verdict(trapped, budget, exp, got)
            # Every vector lands in exactly ONE bucket; main() checks the
            # buckets sum to VECTORS_RUN, so a pass that is not counted
            # anywhere (an uncounted budget pass, say) reds.
            VECTORS_RUN[leg] += 1
            if v == "budget":
                # The ONLY path to a non-compared pass, and it is counted.
                BUDGET[f"{leg} {Path(path).name}:{name}"] += 1
            elif v == "disagree":
                OUTCOMES[leg]["disagree"] += 1
            elif trapped:
                OUTCOMES[leg]["trap"] += 1
            elif rs:
                COMPARED[leg] += 1
            else:
                OUTCOMES[leg]["void"] += 1
            if v == "disagree":
                problems.append(
                    (got[0], f"{Path(path).name}:{name}{tuple(args)} = {describe(got)} expect "
                             f"{'trap' if trapped else '-' if exp is None else hex(exp)}"))
    return ran, problems


def run_exec(path, wasm_bytes, label, model, only=None):
    ran, problems = execute(path, wasm_bytes, model, label, only=only)
    for _, msg in problems:
        fail(f"{label} {msg}")
    return ran


# ---- leg D -----------------------------------------------------------------
def leg_d(td):
    # (1) the classifier, on synthetic bytes, each in a FRESH Uc.
    # 0xB800 is a 16-bit undefined encoding that is NOT UDF: a classifier
    # widened from "16-bit UDF" to "any 16-bit halfword" reads it as a trap.
    for what, code, want in (("udf #0", struct.pack("<HH", 0x2001, 0xDE00), "trap"),
                             ("and.w", struct.pack("<HHH", 0x2001, 0xEA00, 0x0001), "illegal"),
                             ("0xb800 (16-bit undefined, not UDF)",
                              struct.pack("<HH", 0x2001, 0xB800), "illegal")):
        mu = make_uc(M0_MODEL)
        mu.mem_map(CODE, 0x1000)
        mu.mem_map(STK, 0x10000)
        mu.mem_write(CODE, code + b"\x00\xbf\x00\xbf")
        r = run_one(mu, CODE, CODE + len(code), [], [])
        if r[0] != want:
            fail(f"D classifier: `{what}` on the M0 model = {describe(r)}, must be {want}")
        else:
            print(f"D classifier: `{what}` -> {describe(r)}")
    # (2) the comparator, on every outcome kind. Pure: no emulation.
    outcomes = {"ok": ("ok", 5), "ok-wrong": ("ok", 6), "trap": ("trap", 0),
                "illegal": ("illegal", 0, 0xEA00), "fault": ("fault", "x"), "hang": ("hang", 0)}
    want = {
        # (trapped, budget) -> outcome -> verdict
        (False, False): {"ok": "agree", "ok-wrong": "disagree", "trap": "disagree",
                         "illegal": "disagree", "fault": "disagree", "hang": "disagree"},
        (True, False): {"ok": "disagree", "ok-wrong": "disagree", "trap": "agree",
                        "illegal": "disagree", "fault": "disagree", "hang": "disagree"},
        (True, True): {"ok": "disagree", "ok-wrong": "disagree", "trap": "disagree",
                       "illegal": "disagree", "fault": "disagree", "hang": "budget"},
    }
    bad = [(tb, o, verdict(tb[0], tb[1], None if tb[0] else 5, outcomes[o]), w)
           for tb, row in want.items() for o, w in row.items()
           if verdict(tb[0], tb[1], None if tb[0] else 5, outcomes[o]) != w]
    if bad:
        fail(f"D comparator: (trapped, budget), outcome, got, want: {bad}")
    else:
        print(f"D comparator: {sum(len(r) for r in want.values())}/"
              f"{sum(len(r) for r in want.values())} outcome rules hold (UDF-only traps; "
              "budget never passes an illegal, fault or trap)")
    # (3) real v7-M compiler output, through leg C's own harness.
    wat = os.path.join(td, f"potency_{POTENCY_PROBE}.wat")
    Path(wat).write_text(probe_module(POTENCY_PROBE, PROBES[POTENCY_PROBE]))
    o = os.path.join(td, "potency.cortex-m3.o")
    r = synth([wat, "--target", "cortex-m3", *BASE, *EMBED, "-o", o])
    if r.returncode != 0 or POTENCY_PROBE not in load(o)[1]:
        fail(f"D: cortex-m3 did not compile {POTENCY_PROBE}: {r.stderr.strip()[-200:]}")
        return
    text = load(o)[0]
    bad = scan_text(text)
    if not bad or not bad[1].startswith("ea"):
        fail(f"D: the cortex-m3 {POTENCY_PROBE} carrier has no and.w (scan: {bad}); "
             "the potency control would be vacuous")
        return
    src = Path(wat).read_text()
    ran, probs = execute(o, src, M0_MODEL, "D", only={POTENCY_PROBE})
    kinds = collections.Counter(k for k, _ in probs)
    if ran != 1 or kinds != {"illegal": len(VECTORS)}:
        fail(f"D: v7-M {POTENCY_PROBE} on the M0 model must be ILLEGAL on all "
             f"{len(VECTORS)} vectors; got ran={ran} {dict(kinds)} "
             f"{probs[0][1] if probs else 'NO FAULT — the model is not enforcing ARMv6-M'}")
    else:
        print(f"D v7-M and.w on the M0 model: ILLEGAL on {len(VECTORS)}/{len(VECTORS)} "
              f"vectors ({probs[0][1].split(' = ', 1)[1].split(' expect')[0]})")
    ran, probs = execute(o, src, M3_MODEL, "D-control", only={POTENCY_PROBE})
    if ran != 1 or probs:
        fail(f"D control: the same bytes on the M3 model must equal wasmtime; ran={ran} "
             f"{probs[:2]}")
    else:
        print(f"D control: the same bytes on the M3 model equal wasmtime on {len(VECTORS)} vectors")


# ---- leg E -----------------------------------------------------------------
def leg_e(td):
    if len(PROBES) != PROBE_COUNT:
        fail(f"E: {len(PROBES)} probes embedded, pinned {PROBE_COUNT}")
    pdir = os.path.join(td, "probes")
    os.makedirs(pdir)
    accepted = {t: set() for t in (*TARGETS, "cortex-m3")}
    texts = {}
    for name, body in PROBES.items():
        wat = os.path.join(pdir, f"{name}.wat")
        Path(wat).write_text(probe_module(name, body))
        for t in (*TARGETS, "cortex-m3"):
            o = os.path.join(pdir, f"{name}.{t}.o")
            r = synth([wat, "--target", t, *BASE, *EMBED, "-o", o])
            if r.returncode == 0 and os.path.exists(o):
                text, syms, _, _ = load(o)
                if name in syms and syms[name][1] > 0:
                    accepted[t].add(name)
                    texts[(name, t)] = text
    for t in TARGETS:
        if accepted[t] != PROBE_ACCEPTED:
            fail(f"E {t}: probes accepted {sorted(accepted[t])} != pinned "
                 f"{sorted(PROBE_ACCEPTED)} (gained {sorted(accepted[t] - PROBE_ACCEPTED)}, "
                 f"lost {sorted(PROBE_ACCEPTED - accepted[t])})")
    m3_declined = set(PROBES) - accepted["cortex-m3"]
    if m3_declined != PROBE_M3_DECLINED:
        fail(f"E cortex-m3 control: declined {sorted(m3_declined)} != pinned "
             f"{sorted(PROBE_M3_DECLINED)}")
    print(f"E probes: cortex-m0 {len(accepted['cortex-m0'])}, cortex-m0plus "
          f"{len(accepted['cortex-m0plus'])}, cortex-m3 {len(accepted['cortex-m3'])} "
          f"of {len(PROBES)}")
    ran = 0
    for name in sorted(accepted["cortex-m0"] & accepted["cortex-m0plus"]):
        if texts[(name, "cortex-m0")] != texts[(name, "cortex-m0plus")]:
            fail(f"E {name}: cortex-m0 and cortex-m0plus emit different .text")
        o = os.path.join(pdir, f"{name}.cortex-m0.o")
        leg_b(o, f"probe {name}")
        ran += run_exec(o, Path(pdir, f"{name}.wat").read_text(), "E", M0_MODEL, only={name})
    print(f"E probes: {ran} accepted probes executed on the M0 model vs wasmtime")
    # Every accepted probe is register-signature and call-free today; one that
    # silently stops executing would shrink this leg to nothing.
    if ran != len(PROBE_ACCEPTED):
        fail(f"E: executed {ran} of {len(PROBE_ACCEPTED)} accepted probes")
    leg_v(pdir)


# ---- leg V: the value comparison's red half --------------------------------
# Real cortex-m0 bytes from leg E, held against a DELIBERATELY WRONG wasmtime
# reference under the same export name. Each must disagree on EXACTLY the
# vectors where the two functions differ (computed here, independently of the
# harness). Recorded under leg "V", so the real pins and counts never see them.
M32, M64 = (1 << 32) - 1, (1 << 64) - 1
VALUE_CONTROLS = (
    # (label, probe object, wrong body, params, truth, wrong)
    ("wrong expected value: i32.add bytes vs an i32.sub reference", "i32_add",
     "(param i32 i32) (result i32) (i32.sub (local.get 0) (local.get 1))", ["i32", "i32"],
     lambda a, b: (a + b) & M32, lambda a, b: (a - b) & M32),
    ("off-by-one in the result word: i32.add bytes vs add+1", "i32_add",
     "(param i32 i32) (result i32) (i32.add (i32.add (local.get 0) (local.get 1)) (i32.const 1))",
     ["i32", "i32"], lambda a, b: (a + b) & M32, lambda a, b: (a + b + 1) & M32),
    ("dropped i64 high word: i64_ident bytes vs a low-word-only reference", "i64_ident",
     "(param i64) (result i64) (i64.and (local.get 0) (i64.const 0xFFFFFFFF))", ["i64"],
     lambda x: x & M64, lambda x: x & M32),
)


def leg_v(pdir):
    for label, probe, wrong, ps, truth, bad_fn in VALUE_CONTROLS:
        o = os.path.join(pdir, f"{probe}.cortex-m0.o")
        if not os.path.exists(o) or probe not in load(o)[1]:
            fail(f"V {label}: no cortex-m0 object for {probe}; the control is vacuous")
            continue
        slots = aapcs_regs(ps)
        want = sum(truth(*[a & M64 for a in vector_args(ps, slots, k)[1]])
                   != bad_fn(*[a & M64 for a in vector_args(ps, slots, k)[1]])
                   for k in range(len(VECTORS)))
        ran, probs = execute(o, probe_module(probe, wrong), M0_MODEL, "V", only={probe})
        kinds = collections.Counter(k for k, _ in probs)
        if want == 0 or ran != 1 or kinds != {"ok": want}:
            fail(f"V {label}: expected {want} value disagreements on {len(VECTORS)} vectors, "
                 f"got ran={ran} {dict(kinds)} — the value comparison is not potent")
        else:
            print(f"V {label}: {want}/{len(VECTORS)} vectors disagree, as computed")


def main():
    print(f"synth: {SYNTH}")
    check_unicorn()
    probe = make_uc(M0_MODEL)
    print(f"unicorn {unicorn.__version__}: UC_MODE_THUMB, cpu model set {M0_MODEL} before "
          f"mem_map, reads back {probe.ctl_get_cpu_model()} (Cortex-M0; cortex-m0plus runs "
          "on it, see the docstring)")
    with tempfile.TemporaryDirectory() as td:
        # ---- leg A ----------------------------------------------------------
        texts = {}
        for t in TARGETS:
            o = os.path.join(td, f"{t}.o")
            r = synth([str(WAT), "--target", t, *BASE, "-o", o])
            if r.returncode != 0:
                fail(f"A --target {t}: exit {r.returncode}: {r.stderr.strip()[-300:]}")
                continue
            declined = {}
            for line in r.stderr.splitlines():
                if line.startswith("warning: skipping function '"):
                    name = line.split("'")[1]
                    cls = line.split("not an ARMv6-M instruction — ", 1)[-1]
                    hit = [c for c in set(EXPECTED_DECLINES.values()) if cls.startswith(c + " (")]
                    declined[name] = max(hit, key=len) if hit else f"UNPARSED: {line[-160:]}"
                    if "(#1301)" not in line:
                        fail(f"A {t}: decline of {name} does not cite #1301")
            if declined != EXPECTED_DECLINES:
                fail(f"A {t}: declines {declined} != pinned {EXPECTED_DECLINES}")
            _, syms, _, _ = load(o)
            if set(syms) != ACCEPTED:
                fail(f"A {t}: accepted {sorted(syms)} != pinned {sorted(ACCEPTED)}")
            texts[t] = leg_b(o, t)
            print(f"A {t}: {len(syms)} accepted, {len(declined)} declined loudly")
        if len(texts) == 2 and texts["cortex-m0"] != texts["cortex-m0plus"]:
            fail("A: cortex-m0 and cortex-m0plus emit different .text")
        for args, needle in (
            ([str(WAT), "--target", "cortex-m0", "--all-exports"], "supports only `--relocatable`"),
            ([str(WAT), "--target", "cortex-m0", "--cortex-m", "--all-exports"],
             "supports only `--relocatable`"),
            ([str(WAT), "-b", "riscv", "--target", "cortex-m0", *BASE], "does not accept"),
        ):
            r = synth([*args, "-o", os.path.join(td, "x.out")])
            if r.returncode == 0 or needle not in r.stderr:
                fail(f"A refusal {' '.join(args[1:])}: rc={r.returncode} {r.stderr.strip()[-200:]}")
        # ---- leg B potency: planted v7-M MOVW, IT and CBZ must be caught ----
        # IT and CBZ/CBNZ EXECUTE on the unicorn M0 model; this leg is their
        # only guard, so each gets its own plant.
        if "cortex-m0" in texts:
            for what, plant in (("MOVW", struct.pack("<HH", 0xF240, 0x002A)),
                                ("IT ne", struct.pack("<H", 0xBF18)),
                                ("CBZ r0", struct.pack("<H", 0xB100))):
                planted = bytearray(texts["cortex-m0"])
                planted[0:len(plant)] = plant
                if scan_text(bytes(planted)) is None:
                    fail(f"B: planted {what} NOT detected — the static leg is blind")
                else:
                    print(f"B planted {what}: detected")
        # ---- leg D: the model enforces ARMv6-M, the classifier is exact -----
        leg_d(td)
        # ---- leg C: execution ------------------------------------------------
        o = os.path.join(td, "cortex-m0.o")
        fns = (run_exec(o, WAT.read_bytes(), "C", M0_MODEL, only=ACCEPTED)
               if os.path.exists(o) else 0)
        if fns != len(ACCEPTED):
            fail(f"C fixture: executed {fns} of {len(ACCEPTED)} accepted functions")
        corpus_fns = corpus_objs = 0
        files = subprocess.run(["git", "-C", str(ROOT), "ls-files"], capture_output=True,
                               text=True, check=True).stdout.split()
        seen = set()
        for f in files:
            if not f.endswith((".wat", ".wasm")) or f.endswith("armv6m_1301.wat"):
                continue
            data = (ROOT / f).read_bytes()
            h = hashlib.sha256(data).hexdigest()
            if h in seen:
                continue
            seen.add(h)
            co = os.path.join(td, f.replace("/", "__") + ".o")
            r = synth([str(ROOT / f), "--target", "cortex-m0", *BASE, *EMBED, "-o", co])
            if r.returncode != 0 or not os.path.exists(co):
                continue
            if not load(co)[1]:
                continue
            corpus_objs += 1
            leg_b(co, f)
            try:
                corpus_fns += run_exec(co, data, "C", M0_MODEL)
            except SystemExit:
                raise
            except Exception as ex:  # a harness gap is a failure, not a skip
                fail(f"C {f}: harness error {ex!r}")
        print(f"C corpus: {corpus_objs} objects with accepted code, {corpus_fns} functions "
              f"executed vs wasmtime on the M0 model ({len(VECTORS)} vectors each)")
        if corpus_fns == 0:
            fail("C corpus: executed nothing")
        print(f"C budget: {sum(BUDGET.values())} vectors unchecked because wasmtime ran out "
              f"of fuel ({FUEL}) — {dict(BUDGET) or 'none'}")
        # (the exact pin is checked once legs C and E have both run)
        # ---- leg E: per-op probes (and leg V, the value red half) -----------
        leg_e(td)
    # ---- the binding: what legs C, E and V actually executed on ---------------
    for leg in ("C", "E", "V"):
        if EXEC_MODELS[leg] != {M0_MODEL}:
            fail(f"binding: leg {leg} executed on CPU model(s) {sorted(EXEC_MODELS[leg])}, "
                 f"must be exactly {{{M0_MODEL}}} (Cortex-M0)")
    print(f"binding: legs C/E/V ran on model(s) {sorted(EXEC_MODELS['C'] | EXEC_MODELS['E'] | EXEC_MODELS['V'])}")
    n_cmp = COMPARED["C"] + COMPARED["E"]
    print(f"#1301 M0ORACLE VALUE-COMPARISONS={n_cmp} (C {COMPARED['C']}, E {COMPARED['E']}; "
          f"floor {VALUE_COMPARISONS_FLOOR})")
    if n_cmp < VALUE_COMPARISONS_FLOOR:
        fail(f"value comparisons {n_cmp} < floor {VALUE_COMPARISONS_FLOOR}")
    for leg in ("C", "E"):
        n_budget = sum(n for k, n in BUDGET.items() if k.split(" ", 1)[0] == leg)
        parts = COMPARED[leg] + sum(OUTCOMES[leg].values()) + n_budget
        print(f"partition {leg}: {VECTORS_RUN[leg]} vectors = {COMPARED[leg]} compared + "
              f"{dict(OUTCOMES[leg])} + {n_budget} budget")
        if parts != VECTORS_RUN[leg]:
            fail(f"partition {leg}: {VECTORS_RUN[leg]} vectors run but {parts} accounted for — "
                 "an outcome passed without being counted")
    if dict(BUDGET) != BUDGET_EXPECTED:
        fail(f"budget: vectors {dict(BUDGET)} != pinned {BUDGET_EXPECTED} "
             f"(new {sorted(set(BUDGET) - set(BUDGET_EXPECTED))}, "
             f"gone {sorted(set(BUDGET_EXPECTED) - set(BUDGET))}, or a count moved)")
    else:
        print(f"budget: {sum(BUDGET.values())} vectors over {len(BUDGET)} functions, "
              "exactly the pinned set")
    print("ORACLE:", "PASS" if not FAILS else f"FAIL ({len(FAILS)})")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
