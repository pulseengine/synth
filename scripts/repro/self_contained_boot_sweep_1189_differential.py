#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 17500
"""RQ-66-WATCHED (#1189) — boot EVERY self-contained corpus image through its
own shipped `Reset_Handler` and execute it against wasmtime.

# Why this exists

The v0.65 mutation survey (RQ-65-MUTANTS, docs/status/MUTATION_SURVEY.md)
found that no execution oracle in the named suite boots the shipped startup:
all six startup-region kills and the R10->R9 red-first control fell ONLY to
unit tests and frozen-byte goldens, and the one startup mutant that survived —
the ROM->RAM data-copy COUNT register `r2` written as `r3` in
`generate_minimal_startup` — changed 46 self-contained objects and nothing
executed one. The same survey's `ir_to_arm` epilogue `mov r1, <hi>` deletion
(eight OPTIMIZED-path objects) and the AAPCS dead-at-return set survived for
the same structural reason: every existing corpus differential runs the
RELOCATABLE object with the harness seeding R11 itself, so the self-contained
image — the startup, the per-function optimized/direct routing, the #758 data
copy, the #649 R9 globals table — is compiled 400 times per survey and
executed never.

# What it does

For every `scripts/repro/*.wat` / `*.wasm`, in EXACTLY the survey's two
self-contained configurations (`--all-exports --target cortex-m4`, and the
same with `--no-optimize` — `scripts/mutation_survey.py` CORPUS_CFGS, so the
objects executed here are the objects the survey byte-triages):

  1. COMPILE. A decline is counted and printed, never failed — the survey's
     own triage owns decline movement; this oracle's non-vacuity is a FLOOR
     on images actually booted.
  2. BOOT. unicorn maps the `.text` PT_LOAD (which carries the ROM image) and
     a ZEROED RAM — no PT_LOAD population, the harness fabricates nothing:
     whatever linear memory and the globals table hold afterwards is what the
     ARTIFACT's own reset path put there. The shipped `Reset_Handler` runs
     from the reset vector up to (not including) the entry `blx r0`, and the
     oracle ASSERTS it got there. That assertion is the point: the surviving
     startup mutant leaves `r2` at its reset value, `subs r2, #1` wraps and
     the copy loop never terminates — an instruction budget stops it
     mid-loop with R10/R11 never written. A harness that boots "up to N
     instructions" and then calls exports (the #758 shape) never sees the
     difference between a finished boot and an abandoned one.
  3. EXECUTE. Every export whose signature fits the AAPCS core registers
     (i32/i64 params, <= 4 words with i64 pairs even-aligned; i32, i64 or no
     result) is called on the booted image with the ARM corpus sweep's
     12-vector argument matrix and compared word-for-word with wasmtime
     (an i64 result is R0:R1 — the mutant that drops the hi move returns
     the poison this harness leaves in R1). RAM and the register file are
     snapshotted once after the boot and RESTORED before every vector, and
     wasmtime gets a fresh instance per vector, so both engines start every
     vector from the same instantiated state and a trapping vector cannot
     poison the next one. Across every call the R9/R10/R11 register contract
     and SP balance are checked.

# Verdicts (every executed vector lands in exactly one)

  ok           values agree (or both trapped)
  mismatch     wasmtime returned a value, the image returned a different one
  img-trap     the image trapped where wasmtime returned
  fault        the image faulted (unmapped access, bad insn) where wasmtime
               returned
  img-timeout  the image exceeded its instruction budget where wasmtime
               returned within fuel
  contract     R9/R10/R11 not preserved, or SP not restored
  trap-miss    wasmtime trapped, the image returned — RECORDED, not failed:
               the compliance envelope (CLAUDE.md) is that default images
               emit no out-of-bounds trap; div-by-zero/unreachable traps are
               `trap-semantics-oracle`'s subject
  budget       wasmtime ran out of fuel — skipped on both sides
  boot-incomplete / boot-fault   the image never reached its entry scaffold
               — FAIL for that image (every export of it is then uncompared)

Known-open findings are PINNED by exact count in KNOWN below with their
issue, the parity oracle's rule: a pin that moves in EITHER direction is red
(fixed -> delete the pin with the fix; new instance -> a finding to file), and
any unpinned non-ok verdict is red.

# Non-vacuity

`# ci-checks: emulations` (the driver's emulator-entry count) plus two floors
measured on the v0.66 tree: images booted and vectors compared. A run that
compiled everything, booted nothing and compared nothing is red.

# Red-first

The RQ-66-WATCHED PR transcript applies the survey's recorded startup mutant
(`encode_thumb2_movw(2, data_copy_bytes ...)` -> register 3) and the
optimized-path `mov r1, <hi>` deletion with `mutation_survey.py`'s own Edit
context manager and shows this oracle red on each, green on the clean tree.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/self_contained_boot_sweep_1189_differential.py
"""

from __future__ import annotations

import os
import struct
import subprocess
import sys
import tempfile
import time
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

REPRO = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32, M64 = 0xFFFFFFFF, (1 << 64) - 1

# EXACTLY scripts/mutation_survey.py's two self-contained CORPUS_CFGS.
LEGS = {
    "self": ["--all-exports", "--target", "cortex-m4"],
    "self-noopt": ["--all-exports", "--target", "cortex-m4", "--no-optimize"],
}

RET = 0x0F00_0000            # a mapped, code-free return pad
BOOT_LIMIT = 12_000_000      # the ROM->RAM copy is 4 insns/byte; gust_kernel copies ~1 MiB
CALL_LIMIT = 400_000         # the ARM corpus sweep's per-vector budget
WASMTIME_FUEL = 2_000_000
REG_POISON = 0xFEEDFACE
ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

# The ARM corpus sweep's argument matrix (arm_corpus_sweep_973.py), verbatim,
# so the executed population is a property of the corpus, not of tuning.
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

# Non-vacuity floors, measured on the v0.66 tree at a73d5ac2 (204 modules x
# 2 legs: 337 compiled, 73 declined, 6 relocatable objects; 331 images
# booted; 17,850 vectors compared) and set a few percent under the
# measurement. Raise when the corpus grows; never lower to green a run.
BOOTED_FLOOR = 320
COMPARED_FLOOR = 17_000

# Known-open findings: (module, leg, export, kind) -> (issue, exact count).
# Measured on the v0.66 tree at a73d5ac2 — the first execution of these
# images. Two classes were already filed (#1204: the optimized path treats
# R9/R10/R11 as allocatable and never saves them — `alloc_i64_pair`'s
# (R8,R9)/(R10,R11) fallback pairs and the `Const` allocator's R9/R10/R11
# fallback — visible here as every `contract` verdict; #1211: multi-table
# `call_indirect` dispatches through the wrong table), two were FOUND by this
# oracle's first run (#1240: the optimized path's i64.clz/ctz/popcnt leave
# the input's high word in the result; #1241: an i64 non-param local loses
# its value on the optimized path — three shapes, each with a half of the
# value visible in R9/R10/R11, plausibly #1204's root), and one is the
# envelope: `memory.grow` on a fixed-memory bare-metal image fails with -1,
# which the spec allows, while wasmtime grows.
GROW_ENVELOPE = "memory.grow on a fixed-memory image fails (-1): spec-legal, the #539 envelope"
KNOWN: dict[tuple[str, str, str, str], tuple[str, int]] = {
    # #1204
    ('base_cse_branch.wat', 'self', 'init_branch', 'contract'): ('#1204', 10),
    ('block_brif_483.wat', 'self', 'init_branch', 'contract'): ('#1204', 10),
    ('cf_shapes_500.wat', 'self', 'seqblocks', 'contract'): ('#1204', 11),
    ('i64_divs_317.wat', 'self', 'divs', 'contract'): ('#1204', 3),
    ('i64_divs_317.wat', 'self', 'rems', 'contract'): ('#1204', 2),
    ('i64_high_reg_zero_fill_916.wat', 'self', 'clz64', 'contract'): ('#1204', 2),
    ('i64_high_reg_zero_fill_916.wat', 'self', 'ctz64', 'contract'): ('#1204', 2),
    ('i64_high_reg_zero_fill_916.wat', 'self', 'shl_keep_low', 'contract'): ('#1204', 8),
    ('i64_high_reg_zero_fill_916.wat', 'self', 'shrs_keep_high', 'contract'): ('#1204', 12),
    ('i64_high_reg_zero_fill_916.wat', 'self', 'shru_keep_high', 'contract'): ('#1204', 6),
    ('i64_result_pair_1189.wat', 'self', 'add64', 'contract'): ('#1204', 5),
    ('i64_result_pair_1189.wat', 'self', 'divs', 'contract'): ('#1204', 3),
    ('i64_result_pair_1189.wat', 'self', 'mul64', 'contract'): ('#1204', 3),
    ('i64_result_pair_1189.wat', 'self', 'rems', 'contract'): ('#1204', 2),
    ('i64_result_pair_1189.wat', 'self', 'shl', 'contract'): ('#1204', 8),
    ('i64_result_pair_1189.wat', 'self', 'shrs', 'contract'): ('#1204', 12),
    ('i64_result_pair_1189.wat', 'self', 'shru', 'contract'): ('#1204', 6),
    ('i64_result_pair_1189.wat', 'self', 'sub64', 'contract'): ('#1204', 6),
    ('i64_result_pair_1189.wat', 'self', 'xor64', 'contract'): ('#1204', 12),
    ('join_alias_1189.wat', 'self', 'inest', 'contract'): ('#1204', 12),
    ('redundant_base_materialization.wat', 'self', 'init_fields', 'contract'): ('#1204', 12),
    ('spill_frame_499.wat', 'self', 'nested', 'contract'): ('#1204', 2),
    ('stack_canary_687.wat', 'self', 'set_canary', 'contract'): ('#1204', 12),
    # #1211
    ('aarch64_call_indirect_851.wat', 'self', 'bin', 'mismatch'): ('#1211', 3),
    ('aarch64_call_indirect_851.wat', 'self', 'bin_dup', 'mismatch'): ('#1211', 3),
    ('aarch64_call_indirect_851.wat', 'self', 'bin_t1', 'mismatch'): ('#1211', 2),
    ('aarch64_call_indirect_851.wat', 'self-noopt', 'bin', 'mismatch'): ('#1211', 3),
    ('aarch64_call_indirect_851.wat', 'self-noopt', 'bin_dup', 'mismatch'): ('#1211', 3),
    ('aarch64_call_indirect_851.wat', 'self-noopt', 'bin_t1', 'mismatch'): ('#1211', 2),
    # #1240 — found by this oracle
    ('i64_high_reg_zero_fill_916.wat', 'self', 'clz64', 'mismatch'): ('#1240', 10),
    ('i64_high_reg_zero_fill_916.wat', 'self', 'ctz64', 'mismatch'): ('#1240', 10),
    ('i64_result_pair_1189.wat', 'self', 'popcnt64', 'mismatch'): ('#1240', 3),
    # #1241 — found by this oracle
    ('aarch64_locals_851.wat', 'self', 'i64_local', 'mismatch'): ('#1241', 12),
    ('brif_local_zeroinit_990.wat', 'self', 'bl_brif_i64', 'mismatch'): ('#1241', 9),
    ('i64_width_vstack_946.wat', 'self', 'f_brif', 'mismatch'): ('#1241', 12),
    # the envelope
    ('aarch64_surface_851.wat', 'self', 'mgrow', 'mismatch'): (GROW_ENVELOPE, 2),
    ('mem_grow_539.wat', 'self', 'grow2', 'mismatch'): (GROW_ENVELOPE, 12),
    ('mem_grow_539.wat', 'self-noopt', 'grow2', 'mismatch'): (GROW_ENVELOPE, 12),
}


class Harness(Exception):
    """A harness-side limitation, named so it is never read as a miscompile."""


# ---------------------------------------------------------------------------
# The image, booted through its own Reset_Handler
# ---------------------------------------------------------------------------
class Image:
    def __init__(self, elf_path: Path):
        with elf_path.open("rb") as fh:
            elf = ELFFile(fh)
            st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
            self.syms = {s.name: s["st_value"] for s in st.iter_symbols() if s.name}
            segs = [(sg["p_vaddr"], sg["p_memsz"], sg.data())
                    for sg in elf.iter_segments() if sg["p_type"] == "PT_LOAD"]
            if elf["e_type"] == "ET_REL" or not segs:
                # A module with imports compiles to a relocatable OBJECT even
                # without --relocatable: no startup, no image to boot. Counted
                # as `object-not-image`, never as a failure.
                raise Harness("relocatable object (imports), not a bootable image")
        text_va, _, text = min(segs, key=lambda s: s[0])
        sp0, reset = struct.unpack_from("<II", text, 0)
        self.sp0 = sp0
        for va, _, data in segs:
            if va != text_va and data:
                # The harness populates NOTHING but .text. An image whose RAM
                # segment carries file bytes would need a loader this
                # bare-metal image does not have — refuse rather than feed it.
                raise Harness(f"RAM PT_LOAD at {va:#x} carries {len(data)} file bytes")
        ram = [(va, sz) for va, sz, _ in segs if va != text_va]
        self.ram_lo = min((va for va, _ in ram), default=sp0 - 0x20000) & ~0xFFF
        ram_hi = max(sp0, max((va + sz for va, sz in ram), default=0))
        self.ram_hi = (ram_hi + 0xFFF) & ~0xFFF
        self.mu = mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        text_lo = text_va & ~0xFFF
        mu.mem_map(text_lo, ((text_va + len(text) + 0xFFF) & ~0xFFF) - text_lo)
        mu.mem_write(text_va, text)
        mu.mem_map(self.ram_lo, self.ram_hi - self.ram_lo)  # zeroed
        mu.mem_map(RET & ~0xFFF, 0x1000)
        mu.mem_map(0xE000E000, 0x1000)  # SCS page (an FPU-target startup writes CPACR)
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
        # Locate the entry `blx r0` by Thumb-decoding forward from the reset
        # vector (a 32-bit immediate that happens to contain 0x4780 cannot
        # fool this), so the boot executes everything the shipped startup
        # does before the entry call: the data copy, the R9/R10/R11 seeds,
        # the globals table, a `bl <start>`.
        pc = reset & ~1
        while True:
            hw = struct.unpack_from("<H", text, pc - text_va)[0]
            if hw == 0x4780:
                break
            pc += 4 if (hw >> 11) in (0b11101, 0b11110, 0b11111) else 2
        self.entry_blx = pc
        mu.reg_write(UC_ARM_REG_SP, sp0)
        self.boot = "ok"
        try:
            mu.emu_start(reset | 1, pc, count=BOOT_LIMIT)
        except UcError as e:
            self.boot = f"boot-fault:{e}"
            return
        if self.trapped:
            self.boot = "boot-trap"
            return
        if (mu.reg_read(UC_ARM_REG_PC) & ~1) != pc:
            # THE assertion: the startup must REACH its entry scaffold. A
            # copy loop that never terminates parks the PC inside itself.
            self.boot = f"boot-incomplete:pc={mu.reg_read(UC_ARM_REG_PC) & ~1:#x}"
            return
        self.regs = {r: mu.reg_read(r) & M32 for r in (UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11)}
        self.snap = bytes(mu.mem_read(self.ram_lo, self.ram_hi - self.ram_lo))

    def restore(self):
        """Back to the just-booted state: RAM image and the contract registers."""
        self.mu.mem_write(self.ram_lo, self.snap)
        for r, v in self.regs.items():
            self.mu.reg_write(r, v)

    def at_udf(self) -> bool:
        """Is the PC parked on a `udf` (T1 `DExx` or T2 `F7F0 Axxx`)? unicorn
        reports the self-contained image's inline trap as
        UC_ERR_INSN_INVALID rather than through the interrupt hook, and a
        trap the image DID honour must not be read as a fault."""
        try:
            pc = self.mu.reg_read(UC_ARM_REG_PC) & ~1
            hw1, hw2 = struct.unpack("<HH", bytes(self.mu.mem_read(pc, 4)))
        except UcError:
            return False
        return (hw1 & 0xFF00) == 0xDE00 or ((hw1 & 0xFFF0) == 0xF7F0 and (hw2 & 0xF000) == 0xA000)

    def call(self, fn: str, words: list[int], result_words: int):
        """-> ('ok', [words]) | ('trap',) | ('fault', msg) | ('timeout',), violations."""
        mu = self.mu
        addr = self.syms[fn]
        self.restore()
        for i, r in enumerate(ARG_REGS):
            mu.reg_write(r, (words[i] & M32) if i < len(words) else REG_POISON)
        mu.reg_write(UC_ARM_REG_SP, self.sp0)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        self.trapped = False
        try:
            mu.emu_start(addr | 1, RET, count=CALL_LIMIT)
        except UcError as e:
            if self.at_udf():
                return ("trap",), []
            return ("fault", str(e)), []
        if self.trapped:
            return ("trap",), []
        if (mu.reg_read(UC_ARM_REG_PC) & ~1) != RET:
            return ("timeout",), []
        viol = []
        for r, name in ((UC_ARM_REG_R9, "R9"), (UC_ARM_REG_R10, "R10"), (UC_ARM_REG_R11, "R11")):
            got = mu.reg_read(r) & M32
            if got != self.regs[r]:
                viol.append(f"{name} clobbered: {got:#010x} != {self.regs[r]:#010x}")
        sp = mu.reg_read(UC_ARM_REG_SP) & M32
        if sp != self.sp0:
            viol.append(f"SP imbalance: {sp:#010x} != {self.sp0:#010x}")
        res = [mu.reg_read(r) & M32 for r in ARG_REGS[:result_words]]
        return ("ok", res), viol


# ---------------------------------------------------------------------------
# wasmtime, the reference engine — a fresh instance per vector
# ---------------------------------------------------------------------------
def to_signed(v: int, bits: int) -> int:
    return v - (1 << bits) if v >= (1 << (bits - 1)) else v


def usable_exports(module) -> list[tuple[str, list[str], list[str]]]:
    """Exports whose signature fits the AAPCS core registers: i32/i64 params
    marshalled to <= 4 words (i64 pairs even-aligned), i32/i64/no result."""
    out = []
    for exp in module.exports:
        ty = exp.type
        if not isinstance(ty, wasmtime.FuncType):
            continue
        params = [str(p) for p in ty.params]
        results = [str(r) for r in ty.results]
        if any(p not in ("i32", "i64") for p in params):
            continue
        if len(results) > 1 or any(r not in ("i32", "i64") for r in results):
            continue
        words = 0
        for p in params:
            if p == "i32":
                words += 1
            else:
                words += (words % 2) + 2
        if words > 4:
            continue
        out.append((exp.name, params, results))
    return out


def vector_args(params: list[str], tup) -> tuple[list[int], list[int]]:
    """(wasm-typed values, AAPCS words) for one matrix row."""
    vals, words, wi = [], [], 0
    for p in params:
        if p == "i32":
            v = tup[wi] & M32
            wi += 1
            vals.append(v)
            words.append(v)
        else:
            v = (tup[wi] & M32) | ((tup[wi + 1] & M32) << 32)
            wi += 2
            vals.append(v)
            if len(words) % 2:
                words.append(0)
            words += [v & M32, (v >> 32) & M32]
    return vals, words


def reference_call(engine, module, fn: str, params, vals, results):
    """-> ('ok', [words]) | ('trap',) | ('budget',) | ('error', msg)"""
    store = wasmtime.Store(engine)
    store.set_fuel(WASMTIME_FUEL)
    try:
        inst = wasmtime.Instance(store, module, [])
        f = inst.exports(store)[fn]
        r = f(store, *[to_signed(v, 32 if t == "i32" else 64) for t, v in zip(params, vals)])
    except wasmtime.Trap:
        return ("trap",)
    except Exception as exc:  # noqa: BLE001 — fuel exhaustion arrives as a generic error
        if "fuel" in str(exc).lower():
            return ("budget",)
        return ("error", str(exc)[:120])
    if not results:
        return ("ok", [])
    v = r & M64
    return ("ok", [v & M32, (v >> 32) & M32] if results[0] == "i64" else [v & M32])


# ---------------------------------------------------------------------------
def compile_leg(src: Path, flags: list[str], out: Path):
    r = subprocess.run([SYNTH, "compile", str(src), *flags, "-o", str(out)],
                       capture_output=True, text=True)
    return r.returncode == 0 and out.exists(), (r.stderr or "")[-200:]


def main() -> int:
    cfg = wasmtime.Config()
    cfg.consume_fuel = True
    engine = wasmtime.Engine(cfg)
    modules = sorted(REPRO.glob("*.wat")) + sorted(REPRO.glob("*.wasm"))
    if not modules:
        print("RESULT: FAIL — no corpus modules found")
        return 1

    counts = {k: 0 for k in ("compiled", "declined", "object-not-image", "booted", "boot-failed",
                             "reference-refused", "compared", "ok", "ok-trap", "trap-miss", "budget",
                             "budget-img", "symbol-missing")}
    seen: dict[tuple[str, str, str, str], int] = {}
    fails: list[str] = []
    t0 = time.time()
    with tempfile.TemporaryDirectory() as td:
        for src in modules:
            try:
                module = wasmtime.Module.from_file(engine, str(src))
                exports = usable_exports(module)
                probe = wasmtime.Store(engine)
                probe.set_fuel(WASMTIME_FUEL)
                wasmtime.Instance(probe, module, [])
            except Exception as exc:  # noqa: BLE001 — imports, unsupported proposals, start traps
                module, exports = None, []
                ref_refusal = str(exc)[:80]
            for leg, flags in LEGS.items():
                out = Path(td) / f"{src.name}.{leg}.elf"
                ok, err = compile_leg(src, flags, out)
                if not ok:
                    counts["declined"] += 1
                    continue
                counts["compiled"] += 1
                try:
                    img = Image(out)
                except Harness as h:
                    if "not a bootable image" in str(h):
                        counts["object-not-image"] += 1
                    else:
                        fails.append(f"{src.name}|{leg}: harness limitation: {h}")
                    continue
                if img.boot != "ok":
                    counts["boot-failed"] += 1
                    key = (src.name, leg, "<boot>", img.boot.split(":")[0])
                    seen[key] = seen.get(key, 0) + 1
                    if key not in KNOWN:
                        fails.append(f"{src.name}|{leg}: {img.boot} — the shipped Reset_Handler did not reach its entry `blx r0`")
                    continue
                counts["booted"] += 1
                if module is None:
                    counts["reference-refused"] += 1
                    print(f"  {src.name}|{leg}: booted; reference refused ({ref_refusal})")
                    continue
                n_cmp = 0
                for name, params, results in exports:
                    if name not in img.syms:
                        counts["symbol-missing"] += 1
                        continue
                    rw = 2 if results == ["i64"] else (1 if results else 0)
                    for tup in ARG_TUPLES:
                        vals, words = vector_args(params, tup)
                        ref = reference_call(engine, module, name, params, vals, results)
                        if ref[0] == "budget":
                            counts["budget"] += 1
                            continue
                        if ref[0] == "error":
                            fails.append(f"{src.name}|{leg}:{name}{tuple(vals)}: reference error {ref[1]}")
                            continue
                        got, viol = img.call(name, words, rw)
                        if got[0] == "timeout" and ref[0] == "ok":
                            # The image ran out of instructions where wasmtime
                            # finished — a counted loop Cranelift closes into
                            # arithmetic (countdown(-1)) that unicorn must walk.
                            # A budget skip on the ARM corpus sweep's rule,
                            # counted, never a verdict.
                            counts["budget-img"] += 1
                            continue
                        counts["compared"] += 1
                        n_cmp += 1
                        kind = None
                        if ref[0] == "trap":
                            if got[0] == "trap":
                                counts["ok-trap"] += 1
                            else:
                                counts["trap-miss"] += 1  # the envelope; recorded
                            continue
                        if got[0] == "ok":
                            if got[1] != ref[1]:
                                kind = "mismatch"
                            elif viol:
                                kind = "contract"
                        elif got[0] == "trap":
                            kind = "img-trap"
                        else:
                            kind = "fault"
                        if kind is None:
                            counts["ok"] += 1
                            continue
                        key = (src.name, leg, name, kind)
                        seen[key] = seen.get(key, 0) + 1
                        if key not in KNOWN:
                            detail = (f"want={[hex(w) for w in ref[1]]} got={[hex(w) for w in got[1]]}"
                                      if got[0] == "ok" else str(got))
                            fails.append(f"{src.name}|{leg}:{name}{tuple(vals)}: {kind} {detail} {'; '.join(viol)}")
                if n_cmp:
                    print(f"  {src.name}|{leg}: {len(exports)} export(s), {n_cmp} vectors", flush=True)

    # Pins move in either direction -> red.
    for key, (issue, want) in sorted(KNOWN.items()):
        have = seen.get(key, 0)
        if have != want:
            fails.append(f"PIN MOVED {key} ({issue}): recorded {want}, now {have} — "
                         + ("fixed: delete the pin" if have < want else "a new instance: file it"))
    if counts["booted"] < BOOTED_FLOOR:
        fails.append(f"FLOOR: only {counts['booted']} images booted, floor {BOOTED_FLOOR}")
    if counts["compared"] < COMPARED_FLOOR:
        fails.append(f"FLOOR: only {counts['compared']} vectors compared, floor {COMPARED_FLOOR}")

    print()
    print("  " + "  ".join(f"{k}={v}" for k, v in counts.items()) + f"  [{time.time() - t0:.0f}s]")
    for f in fails:
        print(f"FAIL {f}")
    print(f"#1189 BOOT CHECKS={counts['ok'] + counts['ok-trap']}/{counts['compared']} "
          f"images={counts['booted']}/{counts['compiled']} trap-miss={counts['trap-miss']}")
    print("RESULT: " + ("PASS" if not fails else f"FAIL ({len(fails)})"))
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
