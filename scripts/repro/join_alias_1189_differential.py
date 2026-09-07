#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 223
"""#1189 — an if/else JOIN register can alias a local's HOME register
(ARM direct selector): silent wrong answer, exit 0, no decline.

THE DEFECT. On the ARM direct selector (`select_with_stack` — every
`--relocatable` compile per #197, and every self-contained function the
optimized path declines and hands down), `local.get` of a register-homed local
pushes the home register ITSELF onto the operand stack, uncopied. When that is
the then-arm's result of an `if (result …) … else …`, the #313 join
`mov R_then, R_else` on the else path writes the LOCAL. A later `local.get` of
that local reads the join value:

      c: mov  r0, r1     <- JOIN writes r0 == local 0's home
      e: adds r2, r0, r0 <- local.get 0 + join, BOTH r0      ir0(0) = 18, want 9

The then-arm is correct only by accident (r0 already holds the value the join
wants), which is why every test taking the then path passed.

MEASURED BLAST RADIUS (main f4780608, base binary, this table — the fixture
below re-executes exactly these bytes every run):

  shape                          arm-reloc   arm-self    rv32-reloc  aarch64
  -----------------------------  ----------  ----------  ----------  -------
  ir0/ir1/ir2/ir3 (home R0..R3)  WRONG       match(*)    match       match
  iboth (both arms are homes)    WRONG       match(*)    match       match
  isets (else writes the local)  WRONG       WRONG(**)   match       match
  inest (two joins)              WRONG x2    match(*)    match       match
  i64p (R0:R1 pair)              WRONG       WRONG(**)   DECLINE     match
  bif (if inside block)          WRONG       match(*)    match       match
  iloop (if inside loop)         WRONG       WRONG(**)   match       match
  iloc (non-param local)         match       match       match       match
  ielse (only else reads home)   match       match       match       match
  idead (no re-read after join)  match       match       match       match
  itee (then-arm local.tee)      match       match       match       match
  bbrif/bfall (#509 block join)  match       match       match       match
  lres (loop result, no join)    match       match       match       match
  icall (function has a call)    match       match       n/a         n/a

  (*)  the OPTIMIZED selector handles a plain `if`/`else` itself (different
       join mechanism); (**) it DECLINES these shapes (`local.set` inside an
       arm, an i64 param pre-gate, a loop back-edge) and falls back to the
       direct selector — the identical bytes, the identical wrong answer.
  Why the clean rows are clean, from the code (each pinned as MATCH here so
  the boundary cannot silently move): RV32 COPIES a param on `local.get`
  (`mv dst, a_n`); AArch64 reconciles into a dedicated reserved slot; a
  NON-PARAM local is promoted only when every access is at control-flow
  depth 0, so a then-arm read is always a frame-slot reload into a fresh
  temp; a function with a `call` frame-backs its params (#204/#193); the
  #509 block join's result register is a fresh temp with the home only ever
  a SOURCE; a `loop (result)` has no join at all; `local.tee` pushes the
  tee'd temp. The class is one site: the then-arm result of a
  value-carrying `if`/`else` being a live register-homed local.

TWO HALVES, ONE CASE TABLE.
  RED half  — the committed fixture holds the objects main's compiler
              emitted for these modules on the ARM legs (see CAPTURE). Every
              run re-executes them under unicorn; the 14 vectors pinned WRONG
              must return EXACTLY the recorded wrong value AND differ from
              live wasmtime (the expansion_canary_gate_1021 discipline), the
              rest must match. This is the permanent proof that the harness
              CAN see the defect — a differential that has never been red is
              a green board of unknown potency.
  LIVE half — the current compiler, all four legs (+ the call module on the
              two ARM legs): every vector must match wasmtime. RED on main
              (ir0(0) -> 0x12, wasmtime 0x9, …), green once the join is fixed.
              RV32's refusal of the i64-param module (#312, surfacing as the
              #952 skipped-export error) is pinned as a recorded decline, not
              manufactured into a wrong answer.

EVERY expected value comes from wasmtime FIRST, live, so the table cannot
drift. Every general-purpose register the ABI does not assign is seeded with a
canary that NAMES it (0xC0DE0000 | index) so an uninitialised read is legible.

WHAT THE `# ci-checks: emulations` FLOOR CAN AND CANNOT SEE. It counts unicorn
entries across both halves (74 fixture + 149 live = 223). It cannot see the
wrong/match partition (a fixture that started matching wasmtime — rot — would
keep the count), nor the RV32 decline (#1113: a refused compile emulates
nothing), nor a live leg quietly dropped in favour of the fixture. Each
carries an in-script floor (`silent-wrong vectors == 14`, `refusals == 1`,
`live vectors == 149`, all DERIVED from the tables above, never typed twice)
and ci.yml greps the printed lines (the #1112 pattern).

CAPTURE (how the fixture was made, and how to remake it):
  git worktree add /tmp/pre1189 f4780608 && cd /tmp/pre1189
  cargo build --features riscv --bin synth
  python scripts/repro/join_alias_1189_differential.py \
      --capture /tmp/pre1189/target/debug/synth --rev f4780608
Capture records; the run asserts.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/join_alias_1189_differential.py
"""

import base64
import io
import json
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_ARCH_ARM64,
    UC_ARCH_RISCV,
    UC_MODE_ARM,
    UC_MODE_RISCV32,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn import arm64_const as a64
from unicorn import arm_const as ac
from unicorn import riscv_const as rc

HERE = Path(__file__).parent
FIXTURE = HERE / "join_alias_1189_red_main.json"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

MODULES = {
    "main": HERE / "join_alias_1189.wat",
    "i64": HERE / "join_alias_1189_i64.wat",
    "call": HERE / "join_alias_1189_call.wat",
}
LEG_FLAGS = {
    "arm-reloc": ["--target", "cortex-m4", "--relocatable", "--all-exports"],
    "arm-self": ["--target", "cortex-m4", "--all-exports"],
    "rv32-reloc": ["-b", "riscv", "--target", "riscv32imac", "--relocatable",
                   "--all-exports"],
    "aarch64": ["-b", "aarch64", "--all-exports"],
}
# Which legs each module runs LIVE. The call module's `bl` relocation is
# resolved by this harness for Thumb only, and the mechanism it controls for
# (param frame-backing under a call) is ARM-direct-selector specific.
LIVE_LEGS = {
    "main": ["arm-reloc", "arm-self", "rv32-reloc", "aarch64"],
    "i64": ["arm-reloc", "arm-self", "rv32-reloc", "aarch64"],
    "call": ["arm-reloc", "arm-self"],
}
# (module, leg) pairs the live half must REFUSE, with the needle that names
# why. RV32 declines an i64 param (#312); #952 then fails the module.
LIVE_DECLINES = {("i64", "rv32-reloc"): "stack type mismatch at op I32WrapI64"}
# The fixture (RED half) holds main's objects for the two ARM legs.
FIXTURE_LEGS = [("main", "arm-reloc"), ("main", "arm-self"),
                ("i64", "arm-reloc"), ("i64", "arm-self")]

CODE, LIN = 0x100000, 0x40000
LINMEM_SELF = 0x20000100  # the optimized path's absolute linear-memory base
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000
RET_PAD = CODE + 0x38000
RET_FLAT = 0x200000
M32, M64 = 0xFFFFFFFF, 0xFFFFFFFFFFFFFFFF
MEM_POISON = 0xDEADBEEF
R_ARM_THM_CALL, R_ARM_THM_JUMP24 = 10, 30

# fn -> ([arg widths in bits], ret width in bits)
I1, I2, I3, I4 = ([32], 32), ([32, 32], 32), ([32, 32, 32], 32), ([32] * 4, 32)
SIGS = {
    "ir0": I1, "ir1": I2, "ir2": I3, "ir3": I4, "iboth": I2, "isets": I1,
    "inest": I2, "bif": I1, "iloop": I2, "iloc": I1, "ielse": I1,
    "idead": I1, "itee": I1, "bbrif": I1, "bfall": I1, "lres": I2,
    "i64p": ([64], 64), "icall": I1,
}
FN_MODULE = {fn: "main" for fn in SIGS}
FN_MODULE["i64p"] = "i64"
FN_MODULE["icall"] = "call"

# ── THE case table: (fn, args, path taken). Every leg, both halves. ─────────
CASES = [
    ("ir0", [0], "else"), ("ir0", [1], "then"), ("ir0", [5], "then"),
    ("ir1", [0, 3], "else"), ("ir1", [1, 3], "then"),
    ("ir2", [0, 0, 3], "else"), ("ir2", [1, 0, 3], "then"),
    ("ir3", [0, 0, 0, 3], "else"), ("ir3", [1, 0, 0, 3], "then"),
    ("iboth", [0, 3], "else"), ("iboth", [1, 3], "then"),
    ("isets", [0], "else"), ("isets", [1], "then"),
    ("inest", [0, 0], "outer-else"), ("inest", [1, 0], "inner-else"),
    ("inest", [1, 1], "then/then"),
    ("bif", [0], "else"), ("bif", [1], "then"),
    ("iloop", [0, 2], "else"), ("iloop", [1, 2], "then"),
    ("iloc", [0], "else"), ("iloc", [1], "then"),
    ("ielse", [0], "else"), ("ielse", [1], "then"),
    ("idead", [0], "else"), ("idead", [1], "then"),
    ("itee", [0], "else"), ("itee", [1], "then"),
    ("bbrif", [0], "fall"), ("bbrif", [5], "taken"),
    ("bfall", [0], "fall"), ("bfall", [5], "taken"),
    ("lres", [3, 2], "2 iters"), ("lres", [3, 1], "1 iter"),
    ("i64p", [0], "else"), ("i64p", [1], "then"),
    ("i64p", [0x100000005], "then"),
    ("icall", [0], "else"), ("icall", [1], "then"),
]

# ── the RED matrix: what main's bytes return on the vectors that reach the
# class. Everything not listed here is pinned MATCH in the fixture half. A
# "wrong" vector must (a) equal the recorded value and (b) differ from live
# wasmtime — "do not manufacture a wrong answer you did not observe".
PINNED_WRONG = {
    ("arm-reloc", "ir0", (0,)): 0x12,
    ("arm-reloc", "ir1", (0, 3)): 0x12,
    ("arm-reloc", "ir2", (0, 0, 3)): 0x12,
    ("arm-reloc", "ir3", (0, 0, 0, 3)): 0x12,
    ("arm-reloc", "iboth", (0, 3)): 0x9,
    ("arm-reloc", "isets", (0,)): 0x12,
    ("arm-reloc", "inest", (0, 0)): 0x12,
    ("arm-reloc", "inest", (1, 0)): 0xE,
    ("arm-reloc", "bif", (0,)): 0x12,
    ("arm-reloc", "iloop", (0, 2)): 0x12,
    ("arm-reloc", "i64p", (0,)): 0x12,
    # self-contained: only the shapes the optimized path DECLINES reach the
    # direct selector's join.
    ("arm-self", "isets", (0,)): 0x12,
    ("arm-self", "iloop", (0, 2)): 0x12,
    ("arm-self", "i64p", (0,)): 0x12,
}
EXPECTED_WRONG = len(PINNED_WRONG)
EXPECTED_REFUSALS = len(LIVE_DECLINES)
EXPECTED_LIVE = sum(
    len(LIVE_LEGS[m]) * sum(1 for fn, _a, _n in CASES if FN_MODULE[fn] == m)
    for m in MODULES
) - sum(
    sum(1 for fn, _a, _n in CASES if FN_MODULE[fn] == m) for (m, _l) in LIVE_DECLINES
)


def canary(i):
    """A value that NAMES the register it seeds."""
    return (0xC0DE0000 | i) & M32


def die(msg):
    print(f"FATAL: {msg}")
    sys.exit(1)


# ── ELF loading (one loader for fixture objects and live objects) ───────────
def encode_thm_bl(pc_at_reloc, target):
    off = (target - (pc_at_reloc + 4)) & 0x01FFFFFF
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    imm10, imm11 = (off >> 12) & 0x3FF, (off >> 1) & 0x7FF
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return 0xF000 | (s << 10) | imm10, 0xD000 | (j1 << 13) | (j2 << 11) | imm11


def load_object(data, leg):
    """(symbols, .text bytes, .text base). A Thumb `bl` to a local symbol is
    resolved in place (the call module); any other relocation is fatal — this
    harness executes what it can see."""
    e = ELFFile(io.BytesIO(data))
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
    sec = e.get_section_by_name(".text")
    base = sec["sh_addr"]
    text = bytearray(sec.data())
    for rel in e.iter_sections():
        if rel["sh_type"] not in ("SHT_REL", "SHT_RELA"):
            continue
        for r in rel.iter_relocations():
            name = symtab.get_symbol(r["r_info_sym"]).name
            if (leg.startswith("arm")
                    and r["r_info_type"] in (R_ARM_THM_CALL, R_ARM_THM_JUMP24)
                    and name in syms):
                off = r["r_offset"]
                hw1, hw2 = encode_thm_bl(CODE + off,
                                         CODE + ((syms[name] - base) & ~1))
                struct.pack_into("<HH", text, off, hw1, hw2)
            else:
                die(f"unresolvable relocation type {r['r_info_type']} -> "
                    f"{name!r} on leg {leg}")
    return syms, bytes(text), base


# ── emulators ───────────────────────────────────────────────────────────────
def _pack_args32(write, regs, widths, args):
    """AAPCS/ilp32 core-register argument marshalling: a 64-bit value takes
    an even-aligned register pair, lo first."""
    ri = 0
    for w, a in zip(widths, args):
        if w == 32:
            write(regs[ri], a & M32)
            ri += 1
        else:
            if ri % 2:
                ri += 1
            write(regs[ri], a & M32)
            write(regs[ri + 1], (a >> 32) & M32)
            ri += 2


def run_arm(obj, name, sig, args, self_contained):
    syms, text, base = obj
    if name not in syms:
        return None, f"symbol {name} missing from .symtab"
    widths, ret = sig
    addr = (syms[name] - base) & ~1
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x40000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(LINMEM_SELF & ~0xFFFF, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_write(CODE, text)
    mu.mem_write(STACK_BASE,
                 struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    for i in (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12):
        mu.reg_write(getattr(ac, f"UC_ARM_REG_R{i}"), canary(i))
    mu.reg_write(ac.UC_ARM_REG_SP, SP0)
    mu.reg_write(ac.UC_ARM_REG_R11, LINMEM_SELF if self_contained else LIN)
    regs = [ac.UC_ARM_REG_R0, ac.UC_ARM_REG_R1, ac.UC_ARM_REG_R2,
            ac.UC_ARM_REG_R3]
    _pack_args32(mu.reg_write, regs, widths, args)
    mu.reg_write(ac.UC_ARM_REG_LR, RET_PAD | 1)
    try:
        mu.emu_start((CODE + addr) | 1, RET_PAD, count=200_000)
    except UcError as ex:
        return None, str(ex)
    r0 = mu.reg_read(ac.UC_ARM_REG_R0) & M32
    if ret == 64:
        return r0 | (mu.reg_read(ac.UC_ARM_REG_R1) & M32) << 32, ""
    return r0, ""


RV_SEED = [
    (rc.UC_RISCV_REG_T0, 16), (rc.UC_RISCV_REG_T1, 17), (rc.UC_RISCV_REG_T2, 18),
    (rc.UC_RISCV_REG_T3, 19), (rc.UC_RISCV_REG_T4, 20), (rc.UC_RISCV_REG_T5, 21),
    (rc.UC_RISCV_REG_T6, 22),
    (rc.UC_RISCV_REG_S1, 23), (rc.UC_RISCV_REG_S2, 24), (rc.UC_RISCV_REG_S3, 25),
    (rc.UC_RISCV_REG_S4, 26), (rc.UC_RISCV_REG_S5, 27), (rc.UC_RISCV_REG_S6, 28),
    (rc.UC_RISCV_REG_A1, 29), (rc.UC_RISCV_REG_A2, 30), (rc.UC_RISCV_REG_A3, 31),
]


def run_rv32(obj, name, sig, args):
    syms, text, base = obj
    if name not in syms:
        return None, f"symbol {name} missing from .symtab"
    widths, ret = sig
    addr = syms[name] - base
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x40000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_map(RET_FLAT, 0x1000)
    mu.mem_write(CODE, text)
    mu.mem_write(STACK_BASE,
                 struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    for reg, i in RV_SEED:
        mu.reg_write(reg, canary(i))
    mu.reg_write(rc.UC_RISCV_REG_SP, SP0)
    mu.reg_write(rc.UC_RISCV_REG_S11, LIN)
    regs = [rc.UC_RISCV_REG_A0, rc.UC_RISCV_REG_A1, rc.UC_RISCV_REG_A2,
            rc.UC_RISCV_REG_A3]
    _pack_args32(mu.reg_write, regs, widths, args)
    mu.reg_write(rc.UC_RISCV_REG_RA, RET_FLAT)
    try:
        mu.emu_start(CODE + addr, RET_FLAT, count=200_000)
    except UcError as ex:
        return None, str(ex)
    a0 = mu.reg_read(rc.UC_RISCV_REG_A0) & M32
    if ret == 64:
        return a0 | (mu.reg_read(rc.UC_RISCV_REG_A1) & M32) << 32, ""
    return a0, ""


def run_a64(obj, name, sig, args):
    syms, text, base = obj
    if name not in syms:
        return None, f"symbol {name} missing from .symtab"
    widths, ret = sig
    addr = (syms[name] - base) & ~1
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x40000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_map(RET_FLAT, 0x1000)
    mu.mem_write(CODE, text)
    mu.reg_write(a64.UC_ARM64_REG_SP, SP0)
    mu.reg_write(a64.UC_ARM64_REG_LR, RET_FLAT)
    for i in range(0, 16):
        mu.reg_write(getattr(a64, f"UC_ARM64_REG_X{i}"), canary(i))
    regs = [a64.UC_ARM64_REG_X0, a64.UC_ARM64_REG_X1, a64.UC_ARM64_REG_X2,
            a64.UC_ARM64_REG_X3]
    for r, (w, a) in zip(regs, zip(widths, args)):
        mu.reg_write(r, a & (M32 if w == 32 else M64))
    try:
        mu.emu_start(CODE + addr, RET_FLAT, count=200_000)
    except UcError as ex:
        return None, str(ex)
    if ret == 32:
        return mu.reg_read(a64.UC_ARM64_REG_W0) & M32, ""
    return mu.reg_read(a64.UC_ARM64_REG_X0) & M64, ""


def run_leg(leg, obj, name, sig, args):
    if leg.startswith("arm"):
        return run_arm(obj, name, sig, args, leg == "arm-self")
    if leg.startswith("rv32"):
        return run_rv32(obj, name, sig, args)
    return run_a64(obj, name, sig, args)


# ── the reference ───────────────────────────────────────────────────────────
class Reference:
    def __init__(self):
        self.engine = wasmtime.Engine()
        self.cache = {}

    def call(self, fn, args):
        widths, ret = SIGS[fn]
        module = FN_MODULE[fn]
        if module not in self.cache:
            m = wasmtime.Module.from_file(self.engine, str(MODULES[module]))
            store = wasmtime.Store(self.engine)
            inst = wasmtime.Instance(store, m, [])
            self.cache[module] = (store, inst)
        store, inst = self.cache[module]
        f = inst.exports(store)[fn]
        call = []
        for w, a in zip(widths, args):
            if w == 32:
                call.append(struct.unpack("<i", struct.pack("<I", a & M32))[0])
            else:
                call.append(struct.unpack("<q", struct.pack("<Q", a & M64))[0])
        return f(store, *call) & (M32 if ret == 32 else M64)


def compile_module(binary, module, leg, out):
    return subprocess.run(
        [binary, "compile", str(MODULES[module]), *LEG_FLAGS[leg], "-o", out],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )


def fmt(v):
    return f"{v:#x}" if v is not None else "<none>"


# ── capture: build the fixture from main's binary ───────────────────────────
def capture(old_synth, rev):
    fix = {
        "provenance": {
            "issue": "#1189",
            "source_rev": rev,
            "note": "objects emitted by main's compiler for the ARM legs "
                    "(the join-alias bytes); see this oracle's docstring for "
                    "the exact recipe",
        },
        "legs": {},
    }
    for module, leg in FIXTURE_LEGS:
        with tempfile.TemporaryDirectory() as td:
            out = os.path.join(td, "m.o")
            r = compile_module(old_synth, module, leg, out)
            if r.returncode != 0 or not os.path.exists(out):
                die(f"capture: {module}/{leg} did not compile:\n{r.stderr[-600:]}")
            blob = Path(out).read_bytes()
            fix["legs"][f"{module}_{leg}"] = {
                "object_b64": base64.b64encode(blob).decode(),
            }
            print(f"captured {module}/{leg}: {len(blob)} bytes")
    FIXTURE.write_text(json.dumps(fix, indent=2) + "\n")
    print(f"wrote {FIXTURE}")
    return 0


# ── the oracle ──────────────────────────────────────────────────────────────
def main():
    if len(sys.argv) == 5 and sys.argv[1] == "--capture" and sys.argv[3] == "--rev":
        return capture(sys.argv[2], sys.argv[4])
    if len(sys.argv) != 1:
        die(f"usage: {sys.argv[0]} [--capture <main synth> --rev <sha>]")

    ref = Reference()
    fails = 0

    # ── RED half: main's own bytes vs wasmtime ──────────────────────────────
    fix = json.loads(FIXTURE.read_text())
    legs = fix["legs"]
    print(f"== red half: fixture rev {fix['provenance']['source_rev'][:12]} "
          f"(main, pre-fix) ==")
    wrong_seen = fix_match = 0
    pinned_hit = set()
    for module, leg in FIXTURE_LEGS:
        key = f"{module}_{leg}"
        entry = legs.get(key)
        if entry is None or "object_b64" not in entry:
            die(f"fixture leg {key} missing an object; re-capture")
        obj = load_object(base64.b64decode(entry["object_b64"]), leg)
        for fn, args, note in CASES:
            if FN_MODULE[fn] != module:
                continue
            want = ref.call(fn, args)
            got, err = run_leg(leg, obj, fn, SIGS[fn], args)
            if err:
                print(f"  FAIL {key} {fn}{tuple(args)}: emulator error: {err}")
                fails += 1
                continue
            pinned = PINNED_WRONG.get((leg, fn, tuple(args)))
            if pinned is not None:
                ok = got == pinned and got != want
                wrong_seen += ok
                pinned_hit.add((leg, fn, tuple(args)))
                label = ("SILENT-WRONG as pinned" if ok else
                         f"NOT the pinned miscompile (pinned {pinned:#x})")
            else:
                ok = got == want
                fix_match += ok
                label = "matches wasmtime" if ok else "diverged from wasmtime"
            print(f"  {'ok  ' if ok else 'FAIL'} {key} {fn}{tuple(args)}[{note}]"
                  f" -> {fmt(got)} (wasmtime: {want:#x}) — {label}")
            fails += not ok
    missing = set(PINNED_WRONG) - pinned_hit
    if missing:
        print(f"  FAIL pinned wrong vectors never executed: {sorted(missing)}")
        fails += 1

    # ── LIVE half: the current compiler must match wasmtime everywhere ──────
    print("== live half: current compiler vs wasmtime ==")
    live_ok = live_bad = refusals = 0
    for module in MODULES:
        for leg in LIVE_LEGS[module]:
            with tempfile.TemporaryDirectory() as td:
                out = os.path.join(td, "m.o")
                r = compile_module(SYNTH, module, leg, out)
                log = r.stderr + r.stdout
                needle = LIVE_DECLINES.get((module, leg))
                if needle is not None:
                    problems = []
                    if r.returncode == 0:
                        problems.append("exit 0 (accepted)")
                    if r.returncode == 101 or "panicked at" in log:
                        problems.append("PANIC, not a decline")
                    if os.path.exists(out):
                        problems.append("object written despite failure")
                    if needle not in log:
                        problems.append(f"missing needle {needle!r}")
                    if problems:
                        print(f"  FAIL {module}/{leg}: {'; '.join(problems)}")
                        fails += 1
                    else:
                        refusals += 1
                        print(f"  ok   {module}/{leg}: clean decline "
                              f"(rc={r.returncode}, no object, needle present)")
                    continue
                if r.returncode != 0 or not os.path.exists(out):
                    print(f"  FAIL {module}/{leg}: did not compile "
                          f"(rc={r.returncode}):\n{log[-500:]}")
                    fails += 1
                    continue
                obj = load_object(Path(out).read_bytes(), leg)
            for fn, args, note in CASES:
                if FN_MODULE[fn] != module:
                    continue
                want = ref.call(fn, args)
                got, err = run_leg(leg, obj, fn, SIGS[fn], args)
                if err:
                    print(f"  FAIL {module}/{leg} {fn}{tuple(args)}: "
                          f"emulator error: {err}")
                    live_bad += 1
                    continue
                ok = got == want
                live_ok += ok
                live_bad += not ok
                print(f"  {'ok  ' if ok else 'FAIL'} {module}/{leg} "
                      f"{fn}{tuple(args)}[{note}] -> {fmt(got)} "
                      f"(wasmtime: {want:#x})"
                      + ("" if ok else " — SILENT WRONG ANSWER"))
    fails += live_bad

    # ── non-vacuity floors the ci-checks header cannot express ──────────────
    if wrong_seen != EXPECTED_WRONG:
        print(f"VACUOUS: silent-wrong vectors={wrong_seen}, want "
              f"{EXPECTED_WRONG} — the red half no longer demonstrates the "
              f"miscompile it exists to remember")
        return 1
    if fix_match == 0:
        print("VACUOUS: no fixture match vector executed")
        return 1
    if refusals != EXPECTED_REFUSALS:
        print(f"VACUOUS: refusals={refusals}, want {EXPECTED_REFUSALS}")
        return 1
    if live_ok + live_bad != EXPECTED_LIVE:
        print(f"VACUOUS: live vectors executed={live_ok + live_bad}, want "
              f"{EXPECTED_LIVE} — a live leg was dropped")
        return 1

    print(f"\nrefusals: {refusals}")
    print(f"silent-wrong vectors: {wrong_seen} (of {EXPECTED_WRONG} pinned); "
          f"fixture match vectors: {fix_match}")
    print(f"live vectors: {live_ok} matched, {live_bad} diverged "
          f"(of {EXPECTED_LIVE})")
    if fails:
        print(f"RESULT: FAIL ({fails})")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
