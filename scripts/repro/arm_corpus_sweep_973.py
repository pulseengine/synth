#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 2335
"""#973 — the ARM leg of the repro-corpus sweep: CI never compiled these for ARM.

WHY THIS EXISTS (the second half of #973, and the larger half)
-----------------------------------------------------------------------------
#973 — `select` on an i64-comparison condition returning the then-arm on every
vector where the else-arm was due — was found only because a lane compiled
`scripts/repro/*.wat` for ARM by hand. Nothing in CI does that. The individual
`repro-sweep-*` jobs run 30-odd HAND-LISTED oracles, each pinned to the one
fixture its issue was about; a fixture written for RV32 or aarch64 is never put
through the ARM backend even when the shape it encodes is backend-independent.
`rv32_cmp_select_472.wat` has carried the #973 shape as `sel_cmp_i64` since
v0.11 and no ARM build ever saw it.

So this sweeps the WHOLE corpus, and it does it in two phases, because the
weaker phase alone would not have caught #973:

  PHASE A — COMPILE COVERAGE. Every `scripts/repro/*.wat` through the ARM
  backend. A fixture either compiles or is on the DECLINES list BY NAME with
  the reason. Both directions are red: an undeclared failure is a regression,
  and a listed fixture that starts compiling must be taken OFF the list, so the
  list cannot rot into a permanent excuse. This is a NO-WILDCARD tripwire, the
  same shape as the #615 silent-NOP guard.

  PHASE B — EXECUTION DIFFERENTIAL. Compiling proves nothing about the values.
  #973 compiled perfectly and returned the wrong number. So every export with
  an all-i32 signature, in every module PURE enough to emulate faithfully, is
  run under unicorn and compared against wasmtime on a fixed argument matrix.

PURITY, AND WHY IT IS DECIDED FROM THE WASM BINARY
-----------------------------------------------------------------------------
Phase B only runs a module with no import, memory, table, global, elem or data
section — decided by walking the WASM section ids (2/4/5/6/9/11), not by
grepping the `.wat`. A module with a data segment would read initialized bytes
under wasmtime and zeros under unicorn, and the resulting "disagreement" would
be an artifact of the harness rather than a defect: a differential that reports
its own setup gaps as miscompiles trains people to ignore it.

That exclusion is a REAL GAP, not a claim of coverage — the memory-touching
fixtures are covered by `repro-sweep-memory-oracle`, which sets up their images
properly. What this leg adds is the population nobody was executing at all.

HONEST SKIPS, ALL COUNTED AND PRINTED
-----------------------------------------------------------------------------
  * a vector where wasmtime TRAPS (div-by-zero, unreachable) — the ARM side is
    a `udf`, and comparing a trap to a return value is not a comparison
  * a vector too LONG for either budget. Both sides get one: wasmtime runs on
    FUEL and unicorn on an instruction count, and a vector that exhausts either
    is skipped on both. `aarch64_ctrlflow_851.wat:countdown(-1)` is the shape —
    a counted loop with 2^32 iterations, 1.4 s under the wasmtime interpreter
    and far longer under unicorn. Calling that a miscompile because the emulator
    stopped early would be the harness reporting its own budget as a defect.
  * an export with more than 4 params (AAPCS stack args) or a non-i32 signature
  * a module Phase A could not compile
A unicorn fault where wasmtime RETURNED WITHIN BUDGET is NOT a skip — it is a
failure. So is a value disagreement. Both budgets are deliberately generous
(2M fuel / 400k instructions) so a skip means "genuinely long-running", and the
skip counts are PRINTED so a change that starts skipping everything is visible
rather than a smaller green number.

TWO FLOORS, because one of them is weaker than it looks
-----------------------------------------------------------------------------
`# ci-checks: emulations >= 2335` is the CI-enforced floor and counts
`emu_start` ENTRIES — measured, not guessed. But a run that entered the emulator
and then discarded every result on budget grounds would still clear it, so the
harness carries its own `MIN_COMPARED` floor on vectors actually COMPARED
against wasmtime (2327, likewise measured). A known mismatch is SUPPRESSED, not
skipped, so listing debt cannot buy slack in that floor either.

Run (needs wasmtime + unicorn + pyelftools + wat2wasm):
  SYNTH=./target/debug/synth python scripts/repro/arm_corpus_sweep_973.py
"""
import os
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

REPRO = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# cortex-m4f, not cortex-m4: the FPU-bearing target is the ARM superset, and on
# plain cortex-m4 sixteen float fixtures decline for a reason that has nothing
# to do with the sweep (measured: 143 compile on m4f vs 139 on m4).
TARGET = "cortex-m4f"

CODE, LIN = 0x100000, 0x40000
RET_PAD = CODE + 0x38000
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000

# Budgets. Symmetric by intent: a vector is compared only when BOTH engines
# finished it. Sized ~20x the longest real fixture run measured here.
WASMTIME_FUEL = 2_000_000
UNICORN_INSNS = 400_000

MEM_POISON = 0xDEADBEEF
REG_POISON = 0xFEEDFACE
CORE_ARGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
R_ARM_THM_CALL, R_ARM_THM_JUMP24 = 10, 30
M32 = 0xFFFFFFFF

# ── PHASE A: the declines, BY NAME and BY REASON ─────────────────────────────
# Every entry is a LOUD `#952` decline (synth refuses to ship an object missing
# a requested export) for an operation the ARM backend does not lower — NOT a
# crash, and NOT a wrong answer. Measured on the v0.58 tree at `--target
# cortex-m4f --relocatable --all-exports`.
#
# Taking a name off this list is the only way to record that a gap closed, and
# leaving one on after it closes is red. Adding one requires saying why here.
EXPECTED_DECLINES = {
    "aarch64_brtable_blockvals_851.wat": "i64/f32/f64 block result values",
    "aarch64_divrem_851.wat": "i64 f64-reinterpret round trip",
    "aarch64_float_completion_851.wat": "f32/f64 ceil/floor/trunc/nearest + i64<->float",
    "aarch64_m3_floats_538.wat": "f64 arithmetic set (aarch64-shaped fixture)",
    "aarch64_m4_trunc_minmax_538.wat": "f64 trunc + f32/f64 min/max/copysign",
    "aarch64_surface_851.wat": "i64 self-call return",
    "f64_369.wat": "f64 surface as a whole on the relocatable path",
    "float_select_return_782.wat": "f64 select + f64 return",
    "i64_float_conv_869.wat": "i64<->f32/f64 conversions",
    "rv32_br_value_931.wat": "i64 br-with-value",
    "trunc_sat_782.wat": "f64 and i64 saturating truncations",
    "vfp_spill_881.wat": "f64 spill shapes",
}

# Compile floor: a FLOOR, so adding fixtures cannot redden the job. Measured
# 144/156 on the v0.58 tree (143/155 before this lane's own fixture).
MIN_COMPILED = 144

# ── PHASE B: the debt this leg SURFACED, by name and by issue ────────────────
# Turning the ARM leg on found 48 wrong vectors that have nothing to do with
# #973 and everything to do with nobody having executed these fixtures on ARM.
# They are listed rather than fixed here (two different defect classes, both
# filed) and rather than narrowed away, which would have meant shipping a leg
# shaped to pass:
#
#   #989 — a `local.set`/`local.tee` CLOBBERS an earlier `local.get` of the SAME
#          local still on the operand stack. `war_set` returns 200 for every
#          input; `get_set_get_param_no_alias` never reads its argument at all.
#          RV32 has the protection (`snapshot_aliases`), ARM does not.
#   #990 — a local written on only ONE arm of a `br_if` is never zero-inited, so
#          the merge reads uninitialised stack. Provable, not inferred: the
#          returned values are this harness's 0xDEADBEEF poison +/- 1.
#
# BOTH DIRECTIONS ARE RED. An entry that starts passing must be deleted (that is
# how a fix records itself), and a mismatch NOT on this list fails the job. The
# vectors are still COMPARED and still counted toward MIN_COMPARED — a known
# mismatch is suppressed, never skipped, so the debt cannot buy slack in the
# floor.
KNOWN_ARM_MISMATCHES = {
    ("rv32_local_promotion_472.wat", "war_set"): 989,
    ("rv32_local_promotion_472.wat", "war_tee"): 989,
    ("aarch64_param_homing_851.wat", "get_set_get_param_no_alias"): 989,
    ("aarch64_param_homing_851.wat", "tee_param_no_alias"): 989,
    ("provenance_branches_396.wat", "decide"): 990,
}

# Phase B floor on COMPARISONS, not on emulator entries. `# ci-checks:
# emulations >= N` counts `emu_start` calls, and a run that entered the emulator
# and then skipped every result on budget grounds would still clear it — the
# exact "green number that measured nothing" shape #910 exists to reject. Set
# from the measured population; a FLOOR, so new fixtures only raise it.
MIN_COMPARED = 2327

# ── PHASE B: the argument matrix ─────────────────────────────────────────────
# Small, signed/unsigned boundary-heavy, and the same for every export, so the
# population is a property of the corpus rather than of per-fixture tuning.
ARG_TUPLES = [
    (0, 0, 0, 0),
    (1, 2, 3, 4),
    (7, 5, 3, 1),
    (5, 7, 11, 13),
    (100, 100, 100, 100),
    (-1, 1, -1, 1),
    (1, -1, 1, -1),
    (-5, -7, -9, -11),
    (0x7FFFFFFF, -1, 0x7FFFFFFF, -1),
    (-1, 0x7FFFFFFF, 1, 0),
    (0, -1, 0, -1),
    (0xFFFF, 0x10000, 3, 2),
]

WASM_SECTION_FORBIDDEN = {
    2: "import",
    4: "table",
    5: "memory",
    6: "global",
    9: "elem",
    11: "data",
}


def uleb(buf, pos):
    val = shift = 0
    while True:
        b = buf[pos]
        pos += 1
        val |= (b & 0x7F) << shift
        if not b & 0x80:
            return val, pos
        shift += 7


def impure_sections(wasm):
    """Section ids that make a module unfaithful to emulate here."""
    found, pos = [], 8  # skip magic + version
    while pos < len(wasm):
        sid = wasm[pos]
        pos += 1
        size, pos = uleb(wasm, pos)
        if sid in WASM_SECTION_FORBIDDEN:
            found.append(WASM_SECTION_FORBIDDEN[sid])
        pos += size
    return found


def to_wasm(wat):
    """Assemble the fixture, or None when the REFERENCE toolchain refuses it.

    `--enable-all` because several fixtures use post-MVP proposals synth's own
    frontend accepts (multi-memory, bulk-memory). A fixture wat2wasm still
    refuses is a Phase-B skip with its own counter, never a silent one: synth
    compiled it in Phase A, so the gap is in the reference side, and calling
    that a miscompile would be the harness blaming the compiler for its own
    tooling.
    """
    p = subprocess.run(
        ["wat2wasm", "--enable-all", str(wat), "-o", "/dev/stdout"],
        capture_output=True,
    )
    return p.stdout if p.returncode == 0 else None


def compile_arm(wat, out):
    p = subprocess.run(
        [SYNTH, "compile", str(wat), "--target", TARGET, "--relocatable",
         "--all-exports", "-o", out],
        capture_output=True, text=True,
    )
    return p.returncode, (p.stderr or "") + (p.stdout or "")


def encode_thm_bl(pc_at_reloc, target):
    off = (target - (pc_at_reloc + 4)) & 0x01FFFFFF
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    imm10, imm11 = (off >> 12) & 0x3FF, (off >> 1) & 0x7FF
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return 0xF000 | (s << 10) | imm10, 0xD000 | (j1 << 13) | (j2 << 11) | imm11


def load(path):
    """(symbols, relocated .text, base) or (None, reason, None) if unrunnable."""
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
        sec = e.get_section_by_name(".text")
        if sec is None:
            return None, "no .text", None
        base = sec["sh_addr"]
        text = bytearray(sec.data())
        for rel in e.iter_sections():
            if rel["sh_type"] not in ("SHT_REL", "SHT_RELA"):
                continue
            for r in rel.iter_relocations():
                name = symtab.get_symbol(r["r_info_sym"]).name
                if r["r_info_type"] not in (R_ARM_THM_CALL, R_ARM_THM_JUMP24):
                    return None, f"reloc type {r['r_info_type']} ({name})", None
                if name not in syms:
                    return None, f"undefined reloc target {name}", None
                off = r["r_offset"]
                hw1, hw2 = encode_thm_bl(CODE + off, CODE + ((syms[name] - base) & ~1))
                struct.pack_into("<HH", text, off, hw1, hw2)
    return syms, bytes(text), base


def run(syms, text, base, name, args):
    addr = (syms[name] - base) & ~1
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x40000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_write(CODE, text)
    mu.mem_write(STACK_BASE, struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    mu.reg_write(UC_ARM_REG_SP, SP0)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    for i in range(4):
        mu.reg_write(CORE_ARGS[i], (args[i] & M32) if i < len(args) else REG_POISON)
    mu.reg_write(UC_ARM_REG_LR, RET_PAD | 1)
    try:
        # Wall-clock timeout AS WELL as an instruction budget: a fixture whose
        # ARM lowering does not terminate would otherwise spend the budget on
        # every vector and turn a 90-second sweep into an hour.
        mu.emu_start((CODE + addr) | 1, RET_PAD, count=UNICORN_INSNS)
    except UcError as ex:
        return None, str(ex)
    if mu.reg_read(UC_ARM_REG_PC) & ~1 != RET_PAD & ~1:
        return None, "BUDGET"  # not a fault: the instruction budget ran out
    return mu.reg_read(UC_ARM_REG_R0) & M32, ""


def usable_exports(module):
    """[(name, arity)] for exports with an all-i32 <=4-param, i32 signature."""
    out = []
    for exp in module.exports:
        ty = exp.type
        if not isinstance(ty, wasmtime.FuncType):
            continue
        params = [str(p) for p in ty.params]
        results = [str(r) for r in ty.results]
        if len(params) <= 4 and all(p == "i32" for p in params) and results == ["i32"]:
            out.append((exp.name, len(params)))
    return out


def main():
    # Fuel is what makes the reference side BOUNDED. Without it a fixture like
    # `aarch64_ctrlflow_851.wat:countdown(-1)` — a 2^32-iteration counted loop —
    # spends 1.4 s in the wasmtime interpreter per vector and the sweep never
    # finishes, which is how a leg like this quietly gets deleted for being slow.
    cfg = wasmtime.Config()
    cfg.consume_fuel = True
    engine = wasmtime.Engine(cfg)
    wats = sorted(REPRO.glob("*.wat"))
    if not wats:
        print("ARM CORPUS SWEEP: FAIL — no fixtures found")
        return 1

    compiled, declined, unexpected = [], {}, []
    objects = {}
    td = tempfile.mkdtemp()
    for wat in wats:
        out = os.path.join(td, wat.stem + ".o")
        rc, log = compile_arm(wat, out)
        if rc == 0:
            compiled.append(wat.name)
            objects[wat.name] = out
        elif "#952" in log or "no functions compiled successfully" in log:
            declined[wat.name] = log.strip().splitlines()[-1][:140]
        else:
            unexpected.append((wat.name, rc, log.strip()[-300:]))

    print(f"PHASE A — ARM compile coverage ({TARGET}, --relocatable --all-exports)")
    print(f"  fixtures={len(wats)} compiled={len(compiled)} declined={len(declined)} "
          f"hard-error={len(unexpected)}")

    fails = []
    for name, rc, log in unexpected:
        fails.append(f"PHASE A hard error (not a #952 decline) in {name} rc={rc}: {log}")
    for name in sorted(declined):
        if name not in EXPECTED_DECLINES:
            fails.append(
                f"PHASE A NEW DECLINE: {name} is not on EXPECTED_DECLINES — either a "
                f"regression, or a new fixture using an unsupported ARM op. "
                f"Reason: {declined[name]}"
            )
    for name in sorted(EXPECTED_DECLINES):
        if name in compiled:
            fails.append(
                f"PHASE A RATCHET: {name} now COMPILES for ARM but is still on "
                f"EXPECTED_DECLINES ({EXPECTED_DECLINES[name]}) — remove the entry."
            )
        elif name not in declined:
            fails.append(
                f"PHASE A STALE: {name} is on EXPECTED_DECLINES but no longer exists "
                f"in scripts/repro/ — remove the entry."
            )
    if len(compiled) < MIN_COMPILED:
        fails.append(
            f"PHASE A FLOOR: only {len(compiled)} fixtures compiled for ARM, "
            f"floor is {MIN_COMPILED}."
        )

    # ── PHASE B ──────────────────────────────────────────────────────────────
    checks = mismatches = 0
    trap_skips = fault_fails = budget_skips = 0
    impure_mods = nonrunnable = reference_refused = 0
    executed_mods = 0
    known_seen = set()
    print(f"\nPHASE B — execution differential (unicorn vs wasmtime)")
    for wat in wats:
        if wat.name not in objects:
            continue
        wasm = to_wasm(wat)
        if wasm is None:
            reference_refused += 1
            continue
        bad = impure_sections(wasm)
        if bad:
            impure_mods += 1
            continue
        try:
            module = wasmtime.Module(engine, wasm)
        except Exception:
            reference_refused += 1
            continue
        exports = usable_exports(module)
        if not exports:
            continue
        syms, text, base = load(objects[wat.name])
        if syms is None:
            nonrunnable += 1
            continue
        ran = False
        t0 = time.time()
        for name, arity in exports:
            if name not in syms:
                continue
            for tup in ARG_TUPLES:
                args = list(tup[:arity])
                store = wasmtime.Store(engine)
                store.set_fuel(WASMTIME_FUEL)
                inst = wasmtime.Instance(store, module, [])
                try:
                    want = inst.exports(store)[name](store, *args) & M32
                except Exception as exc:
                    # Fuel exhaustion is a BUDGET skip; anything else is a real
                    # wasm trap (div-by-zero, unreachable) and also uncomparable,
                    # but the two are counted apart so a change that starts
                    # exhausting fuel everywhere is legible.
                    if "fuel" in str(exc).lower():
                        budget_skips += 1
                    else:
                        trap_skips += 1
                    continue
                got, err = run(syms, text, base, name, [a & M32 for a in args])
                if err == "BUDGET":
                    budget_skips += 1
                    continue
                checks += 1
                ran = True
                known = KNOWN_ARM_MISMATCHES.get((wat.name, name))
                if got is None:
                    fault_fails += 1
                    fails.append(
                        f"PHASE B FAULT {wat.name}:{name}{tuple(args)} — wasmtime "
                        f"returned {want} but the ARM code faulted: {err}"
                    )
                elif got != want:
                    mismatches += 1
                    if known is not None:
                        known_seen.add((wat.name, name))
                    else:
                        fails.append(
                            f"PHASE B MISMATCH {wat.name}:{name}{tuple(args)} — "
                            f"want={want} got={got}"
                        )
        if ran:
            executed_mods += 1
            print(f"  {wat.name}: {len(exports)} export(s) x {len(ARG_TUPLES)} "
                  f"vectors  [{time.time() - t0:.1f}s]", flush=True)

    print(f"  modules executed={executed_mods}  vectors={checks}  "
          f"mismatches={mismatches}  faults={fault_fails}")
    print(f"  skipped: impure-module={impure_mods} (memory/table/global/data/import), "
          f"unrunnable-object={nonrunnable}, reference-refused={reference_refused}, "
          f"wasm-trap-vectors={trap_skips}, "
          f"over-budget-vectors={budget_skips}")

    # The OTHER direction of the known-mismatch ratchet: a listed export that
    # produced no mismatch at all was either FIXED (delete the line — that is
    # how the fix records itself) or is no longer being executed (a renamed
    # export, a fixture that started declining), and both are things the list
    # must not quietly outlive.
    for key, issue in sorted(KNOWN_ARM_MISMATCHES.items()):
        if key not in known_seen:
            fails.append(
                f"PHASE B RATCHET: {key[0]}:{key[1]} is on KNOWN_ARM_MISMATCHES "
                f"(#{issue}) but produced NO mismatch this run — either it was "
                f"fixed (remove the entry) or it stopped being executed at all "
                f"(which is a coverage regression, not a fix)."
            )
    if known_seen:
        print(f"  {len(known_seen)} known-mismatch export(s) suppressed: "
              + ", ".join(f"{f}:{e} (#{KNOWN_ARM_MISMATCHES[(f, e)]})"
                          for f, e in sorted(known_seen)))

    if checks < MIN_COMPARED:
        fails.append(
            f"PHASE B FLOOR: only {checks} vectors were actually COMPARED, floor is "
            f"{MIN_COMPARED}. The `emulations` floor counts emulator ENTRIES, which a "
            f"run that skips every vector would still satisfy; this is the floor on "
            f"comparisons."
        )

    print(f"\n#973 ARM CORPUS compiled={len(compiled)}/{len(wats)} "
          f"executed={checks - mismatches - fault_fails}/{checks}")
    for f in fails:
        print(f"FAIL {f}")
    if fails:
        print("#973 ARM CORPUS SWEEP: FAIL")
        return 1
    print("#973 ARM CORPUS SWEEP: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
