#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 19
"""#1097 (RQ-61-MVORACLE) — the silent-miscompile evidence behind the #1093
parameter-taking block-type decline, promoted from a lane scratchpad into a
permanent red-first oracle.

WHY THIS EXISTS. #1093 was reported as a PANIC (`if (param ..) .. else`,
"`at` split index (is 2) should be <= len (is 1)"). The class sweep found the
same root cause in shapes that do NOT panic: they compiled, exited 0, and
returned a wrong value — an `if (param i32)` WITHOUT an else read a register
only the then-arm writes, so the false path returned an UNINITIALIZED
REGISTER. #1096 made the whole class decline loudly, which is the right fix —
but the guard plus "it declines" tests demonstrate only conservatism, not
necessity. This oracle re-executes the PRE-#1096 compiler's own emitted bytes
(committed fixture, see CAPTURE below) against wasmtime on every CI run, so
the repo permanently demonstrates WHY the decline is mandatory, and any
future multi-value lowering has an acceptance oracle it must pass before the
guard can be relaxed.

MEASURED MATRIX (rev b2abf951 = c4b463f3^, the tree one commit before the
#1096 merge; `--relocatable --all-exports`, cortex-m4 / riscv32imac):

  shape                     ARM direct selector       RV32 selector
  ------------------------  ------------------------  ------------------------
  if (param i32), no else   SILENT-WRONG: ipe(0) ->   SILENT-WRONG: ipe(0) ->
                            0xC0DE0003 (= uninit R3   uninit T2 canary, want 7
                            canary), want 7
  block (param i32)+br_if   compiled, CORRECT on all  SILENT-WRONG: bpb(1) ->
                            7 probed vectors — the    uninit T2 canary, want 7
                            decline is CONSERVATIVE   (the taken edge drops
                            on this leg (negative     the carried param)
                            result, pinned as MATCH)
  loop (param i32)+br_if    DECLINED pre-#1096 (the   SILENT-WRONG: lpb(3) ->
  back-edge                 #509 value-carrying-      2, want 10 (the back-
                            back-edge decline) —      edge mis-reconciles the
                            never silent (negative    join value)
                            result, pinned as a
                            recorded refusal)

Four SILENT-WRONG legs demonstrated; the two negative results are pinned as
what they are (a correct-on-these-vectors leg and a pre-existing refusal),
per the "do not manufacture a wrong answer you did not observe" rule.

EVERY expected value comes from wasmtime FIRST, live, so the oracle cannot
drift. The pinned WRONG values are additionally asserted EXACTLY (the
expansion_canary_gate_1021 fixture discipline): a wrong vector must (a) equal
the observed pre-#1096 value and (b) differ from live wasmtime. Every
general-purpose register the ABI does not assign is seeded with a canary that
NAMES it (0xC0DE0000 | index), so "returned an uninitialized register" is
legible from the value itself rather than inferred.

GREEN HALF (current compiler): all six legs (3 shapes x 2 backends) must
decline CLEANLY — exit != 0, NOT the panic exit 101, no "panicked at" in
stderr, the shared #1093 needle "PARAMETER-taking block type" present, and NO
object file written. The guard module (supported neighbours: plain
`if (result)`, value-carrying forward `br_if`) must still COMPILE on both
backends and match wasmtime — the decline covers the class, not everything.

WHAT THE `# ci-checks: emulations >= 19` FLOOR CAN AND CANNOT SEE. It counts
unicorn entries: 11 fixture (red) emulations + 8 guard (live) emulations. It
CANNOT see the decline half — a refused compile emulates nothing (#1113), so
deleting the green half would leave the floor met. That half therefore
carries its own in-script floor (refusals == 6, non-zero exit otherwise) and
ci.yml greps the `refusals:` line (the #1112 pattern). The floor also cannot
see that the four wrong vectors stayed wrong — that is the in-script
`silent-wrong vectors == 4` partition check, which fails the run if a
"wrong" vector starts matching wasmtime (fixture rot) or a MATCH vector
stops matching.

CAPTURE (how the fixture was made, and how to remake it):
  git worktree add /tmp/pre1096 c4b463f3^ && cd /tmp/pre1096
  cargo build --features riscv --bin synth
  python scripts/repro/param_block_silent_1097_differential.py \
      --capture /tmp/pre1096/target/debug/synth
The fixture param_block_silent_1097_red_pre1096.json commits the pre-#1096
compiler's emitted objects base64-whole (ELF, read back via pyelftools like
every live object — one loader for both halves) plus the loop/arm refusal it
emitted instead of an object. Capture records; the run asserts.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/param_block_silent_1097_differential.py
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
    UC_ARCH_RISCV,
    UC_MODE_RISCV32,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn import arm_const as ac
from unicorn import riscv_const as rc

HERE = Path(__file__).parent
FIXTURE = HERE / "param_block_silent_1097_red_pre1096.json"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

SHAPES = ("if", "block", "loop")
BACKENDS = ("arm", "rv32")
WATS = {s: HERE / f"param_block_silent_1097_{s}.wat" for s in SHAPES}
GUARD_WAT = HERE / "param_block_silent_1097_guard.wat"

CODE, LIN = 0x100000, 0x40000
RET = 0x200000  # RV32 return sentinel; ARM uses CODE + 0x8000
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000
M32 = 0xFFFFFFFF
MEM_POISON = 0xDEADBEEF
DECLINE_NEEDLE = "PARAMETER-taking block type"


def canary(i):
    """A value that NAMES the register it seeds."""
    return (0xC0DE0000 | i) & M32


# ARM: index == architectural register number (R11 is the linear-memory base,
# SP/LR are set separately; R12 is the sanctioned encoder scratch but is
# seeded too so a stray read of it is legible).
ARM_SEED = [
    (ac.UC_ARM_REG_R0, 0), (ac.UC_ARM_REG_R1, 1), (ac.UC_ARM_REG_R2, 2),
    (ac.UC_ARM_REG_R3, 3), (ac.UC_ARM_REG_R4, 4), (ac.UC_ARM_REG_R5, 5),
    (ac.UC_ARM_REG_R6, 6), (ac.UC_ARM_REG_R7, 7), (ac.UC_ARM_REG_R8, 8),
    (ac.UC_ARM_REG_R9, 9), (ac.UC_ARM_REG_R10, 10), (ac.UC_ARM_REG_R12, 12),
]
ARM_ARGS = [ac.UC_ARM_REG_R0, ac.UC_ARM_REG_R1, ac.UC_ARM_REG_R2, ac.UC_ARM_REG_R3]

# RV32: FIXED order, indices 16.. so no RV canary collides with an ARM one.
# t0..t6 = 16..22, s1..s6 = 23..28, a1..a3 = 29..31 (a0 carries the single
# i32 argument in every fixture; s11 is the linear-memory base).
RV_SEED = [
    (rc.UC_RISCV_REG_T0, 16), (rc.UC_RISCV_REG_T1, 17), (rc.UC_RISCV_REG_T2, 18),
    (rc.UC_RISCV_REG_T3, 19), (rc.UC_RISCV_REG_T4, 20), (rc.UC_RISCV_REG_T5, 21),
    (rc.UC_RISCV_REG_T6, 22),
    (rc.UC_RISCV_REG_S1, 23), (rc.UC_RISCV_REG_S2, 24), (rc.UC_RISCV_REG_S3, 25),
    (rc.UC_RISCV_REG_S4, 26), (rc.UC_RISCV_REG_S5, 27), (rc.UC_RISCV_REG_S6, 28),
    (rc.UC_RISCV_REG_A1, 29), (rc.UC_RISCV_REG_A2, 30), (rc.UC_RISCV_REG_A3, 31),
]
RV_ARGS = [rc.UC_RISCV_REG_A0, rc.UC_RISCV_REG_A1, rc.UC_RISCV_REG_A2]

# ── the red matrix: (shape, backend, export, args, expectation) ─────────────
# "wrong": the pre-#1096 bytes must return EXACTLY this pinned value AND it
#          must differ from live wasmtime — the silent miscompile, re-executed.
# "match": the pre-#1096 bytes must agree with wasmtime — the conservative
#          leg / non-triggering vectors, pinned so they cannot be quietly
#          promoted to "was always broken" without observation.
RED_CASES = [
    # if (param i32) without else: the false path reads a register only the
    # then-arm writes. ARM: uninit R3 canary. RV32: uninit T2 canary.
    ("if", "arm", "ipe", [0], ("wrong", 0xC0DE0003)),
    ("if", "arm", "ipe", [1], ("match", None)),
    ("if", "rv32", "ipe", [0], ("wrong", 0xC0DE0012)),
    ("if", "rv32", "ipe", [1], ("match", None)),
    # block (param i32) + br_if: ARM happened to reconcile this shape
    # (negative result — conservative leg); RV32 drops the carried param on
    # the taken edge and returns the uninit T2 canary.
    ("block", "arm", "bpb", [1], ("match", None)),
    ("block", "arm", "bpb", [0], ("match", None)),
    ("block", "rv32", "bpb", [1], ("wrong", 0xC0DE0012)),
    ("block", "rv32", "bpb", [0], ("match", None)),
    # loop (param i32) + back-edge: correct until the back-edge is TAKEN
    # (lpb(0)/lpb(1) run the body once), then the join value is mangled.
    ("loop", "rv32", "lpb", [0], ("match", None)),
    ("loop", "rv32", "lpb", [1], ("match", None)),
    ("loop", "rv32", "lpb", [3], ("wrong", 0x00000002)),
]
EXPECTED_WRONG = sum(1 for *_x, (kind, _v) in RED_CASES if kind == "wrong")

GUARD_CASES = [("gie", [0]), ("gie", [1]), ("gbr", [0]), ("gbr", [1])]

COMPILE_ARGS = {
    "arm": ["--target", "cortex-m4", "--relocatable", "--all-exports"],
    "rv32": ["-b", "riscv", "--target", "riscv32imac", "--relocatable",
             "--all-exports"],
}


def die(msg):
    print(f"FATAL: {msg}")
    sys.exit(1)


def load_object(data):
    """symbols + .text from ELF bytes. These fixtures are leaf functions:
    any relocation means the fixture is not what this harness executes."""
    e = ELFFile(io.BytesIO(data))
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
    for sec in e.iter_sections():
        if sec["sh_type"] in ("SHT_REL", "SHT_RELA") and sec.num_relocations():
            die("object carries relocations; this harness executes leaf "
                "functions only and resolves none")
    return syms, e.get_section_by_name(".text").data()


def run_arm(syms, text, name, args):
    addr = syms.get(name)
    if addr is None:
        return None, f"symbol {name} missing from .symtab"
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_write(CODE, text)
    mu.mem_write(STACK_BASE,
                 struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    for reg, i in ARM_SEED:
        mu.reg_write(reg, canary(i))
    mu.reg_write(ac.UC_ARM_REG_SP, SP0)
    mu.reg_write(ac.UC_ARM_REG_R11, LIN)  # linear-memory base
    for i, a in enumerate(args):
        mu.reg_write(ARM_ARGS[i], a & M32)
    ret_pad = CODE + 0x8000
    mu.reg_write(ac.UC_ARM_REG_LR, ret_pad | 1)
    try:
        mu.emu_start((CODE + (addr & ~1)) | 1, ret_pad, count=200_000)
    except UcError as ex:
        return None, str(ex)
    return mu.reg_read(ac.UC_ARM_REG_R0) & M32, ""


def run_rv32(syms, text, name, args):
    addr = syms.get(name)
    if addr is None:
        return None, f"symbol {name} missing from .symtab"
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, text)
    mu.mem_write(STACK_BASE,
                 struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    for reg, i in RV_SEED:
        mu.reg_write(reg, canary(i))
    mu.reg_write(rc.UC_RISCV_REG_SP, SP0)
    mu.reg_write(rc.UC_RISCV_REG_S11, LIN)  # linear-memory base
    for i, a in enumerate(args):
        mu.reg_write(RV_ARGS[i], a & M32)
    mu.reg_write(rc.UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + addr, RET, count=200_000)
    except UcError as ex:
        return None, str(ex)
    return mu.reg_read(rc.UC_RISCV_REG_A0) & M32, ""


RUNNERS = {"arm": run_arm, "rv32": run_rv32}


def wasmtime_fn(engine, wat, name):
    module = wasmtime.Module.from_file(engine, str(wat))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    f = inst.exports(store)[name]

    def call(args):
        vals = [a - (1 << 32) if a > 0x7FFFFFFF else a for a in args]
        return f(store, *vals) & M32

    return call


def compile_module(binary, wat, backend, out):
    r = subprocess.run(
        [binary, "compile", str(wat), *COMPILE_ARGS[backend], "-o", out],
        capture_output=True, text=True,
    )
    return r


# ── capture: build the fixture from a pre-#1096 binary ──────────────────────
def capture(old_synth):
    rev = subprocess.run(["git", "-C", str(Path(old_synth).parent),
                          "rev-parse", "HEAD"], capture_output=True, text=True)
    fix = {
        "provenance": {
            "issue": "#1097",
            "source_rev": rev.stdout.strip() or "unknown",
            "note": "objects emitted by the pre-#1096 compiler (c4b463f3^); "
                    "see this oracle's docstring for the exact recipe",
        },
        "legs": {},
    }
    for shape in SHAPES:
        for backend in BACKENDS:
            with tempfile.TemporaryDirectory() as td:
                out = os.path.join(td, f"{shape}_{backend}.o")
                r = compile_module(old_synth, WATS[shape], backend, out)
                if r.returncode == 0 and os.path.exists(out):
                    blob = Path(out).read_bytes()
                    fix["legs"][f"{shape}_{backend}"] = {
                        "object_b64": base64.b64encode(blob).decode(),
                    }
                    print(f"captured {shape}/{backend}: {len(blob)} bytes")
                else:
                    lines = (r.stderr + r.stdout).strip().splitlines()
                    # The per-function refusal reason lives on a "skipping
                    # function" warning line, not the final Error: line.
                    reason = next((ln for ln in lines if "failed:" in ln),
                                  lines[-1] if lines else "")
                    fix["legs"][f"{shape}_{backend}"] = {
                        "declined_rc": r.returncode,
                        "declined_tail": reason.strip(),
                    }
                    print(f"captured {shape}/{backend}: DECLINED "
                          f"rc={r.returncode}")
    FIXTURE.write_text(json.dumps(fix, indent=2) + "\n")
    print(f"wrote {FIXTURE}")
    return 0


# ── the oracle ──────────────────────────────────────────────────────────────
def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--capture":
        return capture(sys.argv[2])
    if len(sys.argv) != 1:
        die(f"usage: {sys.argv[0]} [--capture <pre-1096 synth>]")

    fix = json.loads(FIXTURE.read_text())
    legs = fix["legs"]
    engine = wasmtime.Engine()
    fails = 0

    # ── RED half: the pre-#1096 compiler's own bytes vs wasmtime ───────────
    print(f"== red half: fixture rev {fix['provenance']['source_rev'][:12]} "
          f"(pre-#1096) ==")
    wrong_seen = match_seen = 0
    loaded = {}
    for shape, backend, fn, args, (kind, pinned) in RED_CASES:
        key = f"{shape}_{backend}"
        if key not in loaded:
            leg = legs.get(key)
            if leg is None or "object_b64" not in leg:
                die(f"fixture leg {key} missing an object; re-capture")
            loaded[key] = load_object(base64.b64decode(leg["object_b64"]))
        syms, text = loaded[key]
        want = wasmtime_fn(engine, WATS[shape], fn)(args)
        got, err = RUNNERS[backend](syms, text, fn, args)
        if err:
            print(f"  FAIL {key} {fn}{tuple(args)}: emulator error: {err}")
            fails += 1
            continue
        if kind == "wrong":
            ok = got == pinned and got != want
            wrong_seen += ok
            label = (f"SILENT-WRONG as pinned" if ok else
                     f"NOT the pinned miscompile (pinned {pinned:#010x})")
        else:
            ok = got == want
            match_seen += ok
            label = "matches wasmtime" if ok else "diverged from wasmtime"
        print(f"  {'ok  ' if ok else 'FAIL'} {key} {fn}{tuple(args)} -> "
              f"{got:#x} (wasmtime: {want:#x}) — {label}")
        fails += not ok

    # loop/arm never compiled pre-#1096: the #509 back-edge decline predates
    # #1096. Pinned as a RECORDED refusal so the matrix stays six-legged and
    # honest about which legs were demonstrated silent.
    la = legs.get("loop_arm")
    if not la or "declined_rc" not in la or la["declined_rc"] == 0:
        print("  FAIL loop_arm: fixture must record the pre-#1096 decline")
        fails += 1
    elif "#509" not in la.get("declined_tail", ""):
        print(f"  FAIL loop_arm: recorded decline is not the #509 one: "
              f"{la.get('declined_tail', '')!r}")
        fails += 1
    else:
        print(f"  ok   loop_arm: declined pre-#1096 by #509 (rc="
              f"{la['declined_rc']}) — never silent, nothing to pin wrong")

    # ── GREEN half: current compiler declines all six legs, cleanly ─────────
    print("== green half: current compiler must decline (cleanly) ==")
    refusals = 0
    for shape in SHAPES:
        for backend in BACKENDS:
            with tempfile.TemporaryDirectory() as td:
                out = os.path.join(td, "out.o")
                r = compile_module(SYNTH, WATS[shape], backend, out)
                err = r.stderr + r.stdout
                problems = []
                if r.returncode == 0:
                    problems.append("exit 0 (accepted)")
                if r.returncode == 101 or "panicked at" in err:
                    problems.append("PANIC, not a decline")
                if os.path.exists(out):
                    problems.append("object written despite failure")
                if DECLINE_NEEDLE not in err:
                    problems.append(f"missing needle {DECLINE_NEEDLE!r}")
                if problems:
                    print(f"  FAIL {shape}/{backend}: {'; '.join(problems)}")
                    fails += 1
                else:
                    refusals += 1
                    print(f"  ok   {shape}/{backend}: clean decline "
                          f"(rc={r.returncode}, no object, needle present)")

    # ── guard: the supported neighbours still compile and match wasmtime ────
    print("== guard: the decline covers the class, not everything ==")
    for backend in BACKENDS:
        with tempfile.TemporaryDirectory() as td:
            out = os.path.join(td, "guard.o")
            r = compile_module(SYNTH, GUARD_WAT, backend, out)
            if r.returncode != 0:
                print(f"  FAIL guard/{backend}: DECLINED (rc={r.returncode}) "
                      f"— the guard grew past its class:\n{r.stderr[-400:]}")
                fails += 1
                continue
            syms, text = load_object(Path(out).read_bytes())
        for fn, args in GUARD_CASES:
            want = wasmtime_fn(engine, GUARD_WAT, fn)(args)
            got, err = RUNNERS[backend](syms, text, fn, args)
            ok = err == "" and got == want
            gs = f"{got:#x}" if got is not None else err
            print(f"  {'ok  ' if ok else 'FAIL'} guard/{backend} "
                  f"{fn}{tuple(args)} -> {gs} (wasmtime: {want:#x})")
            fails += not ok

    # ── non-vacuity floors the ci-checks header cannot express ──────────────
    # The emulations floor cannot see the decline half (#1113: a refused
    # compile emulates nothing) nor the wrong/match partition. Both get
    # in-script floors; ci.yml greps the refusals line (#1112 pattern).
    if refusals < len(SHAPES) * len(BACKENDS):
        print(f"VACUOUS: refusals={refusals}, want "
              f"{len(SHAPES) * len(BACKENDS)} — the decline half asserted "
              f"less than the full matrix")
        return 1
    if wrong_seen != EXPECTED_WRONG:
        print(f"VACUOUS: silent-wrong vectors={wrong_seen}, want "
              f"{EXPECTED_WRONG} — the red half no longer demonstrates the "
              f"miscompile it exists to remember")
        return 1
    if match_seen == 0:
        print("VACUOUS: no match vector executed")
        return 1

    print(f"\nrefusals: {refusals}")
    print(f"silent-wrong vectors: {wrong_seen} (of {EXPECTED_WRONG} pinned); "
          f"match vectors: {match_seen}")
    if fails:
        print(f"RESULT: FAIL ({fails})")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
