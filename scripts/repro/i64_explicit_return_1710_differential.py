#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 50000
"""v0.91 I64RET (#1710) — an i64 result leaving the function through an
EXPLICIT exit, EXECUTED against wasmtime on both selectors.

# The defect — two layers

1. The direct selector (`select_with_stack`, which `--relocatable` forces and
   the self-contained path diverts to for an i64 parameter, an `if`, a
   `br_table`, ...) has five places that return from the function: the
   fall-through epilogue, `return`, and a function-level `br`, `br_if` and
   `br_table` edge. Only the fall-through epilogue landed an i64 result's HIGH
   word in R1 (#311 defect 3); the other four each carried their own copy of a
   lo-only `mov r0, val`. An i64 result reaching any of them returned with R1
   holding whatever it last held — for `(return (i64.shl (local.get $x)
   (i64.const 31)))` the high word of `$x` itself. Fixed by routing all five
   through ONE landing, `int_return_moves`.

2. With (1) fixed, the `br_table` exit was STILL wrong: the range
   re-allocator (`reallocate_function_post_exhaust`, default-on) segmented
   straight through a `pop {…, pc}` return, so the dead epilogue after the
   `br_table`'s shared return made the return value's `mov r1, hi`
   segment-locally dead, and it was recoloured to `mov r0, hi`. A return now
   ends its segment (and likewise in `apply_spill_realloc_post_exhaust`).

# The class this executes

Every PRODUCER x every EXIT x every SIGNATURE, generated below (no checked-in
fixture to drift):

  producers — every i64 shift/rotate by a constant and by a variable count,
  add/sub/mul/and/or/xor, the four software div/rem, clz/ctz/popcnt, a
  constant, extend_i32_s/u, extend8/16/32_s, select, the SECOND operand (for
  `w` it lives in r2:r3, so a lo-only move returns a mixed pair), and
  local.tee into an i64 local;

  exits — `fall` (the CONTROL: the fall-through epilogue, correct before the
  fix), `ret` (tail `return`), `ifret` (`return` inside an `if`), `ifelse`
  (`return` in the then-arm of a result-typed if), `br0` (function-level `br`),
  `blkbr` (`br 1` out of a block to the function), `brif` (function-level
  `br_if`, value kept live on the fall-through), `brtable` (function-level
  `br_table`), `loopret` (`return` inside a `loop`), and `retdead` / `brdead`
  (dead code after the exit — the layer-2 shape);

  signatures — `w` (i64, i64 params: the direct selector on every leg), `l`
  (i32, i32 params rebuilt into i64 locals) and `n` (i32, i32 params with the
  i64 operands recomputed inline — the shape the self-contained OPTIMIZED path
  accepts; most `l`/`n` functions take it there, measured with
  SYNTH_PATH_DEBUG=1).

Legs: `--relocatable` on cortex-m4, cortex-m4f, cortex-m7dp (Thumb-2) and
cortex-r5 (A32, run in ARM state) — raw `.text`, relocation-free (asserted) —
and the self-contained image on cortex-m4 and cortex-m7dp, booted through its
own `Reset_Handler`. Every vector runs with the non-argument argument registers
POISONED; R0:R1 is compared with wasmtime's 64-bit result, and SP / R4-R11
must be restored. A vector wasmtime traps on must trap in the image too
(`ok-trap`); a trapping image on a vector wasmtime returns from is a mismatch.

# Non-vacuity

Every generated export must be present in every leg's symtab (a declined
function is a FAIL here, not a skip: the whole class compiles today), and the
compared-vector count must reach COMPARED_FLOOR.

# Red-first

Measured on main e918c711's binary: 23,350 of 52,800 vectors wrong, on every
leg and on every exit EXCEPT the `fall` control (0 wrong). With only layer 1
fixed, the `brtable` exit alone stays red. Both layers fixed: 52,800/52,800.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/i64_explicit_return_1710_differential.py
"""

from __future__ import annotations

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_HOOK_INTR, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as ac

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32, M64 = 0xFFFFFFFF, (1 << 64) - 1
RET = 0x0F00_0000
BOOT_LIMIT = 1_000_000
CALL_LIMIT = 200_000
POISON = 0xFEEDFACE
ARG_REGS = [ac.UC_ARM_REG_R0, ac.UC_ARM_REG_R1, ac.UC_ARM_REG_R2, ac.UC_ARM_REG_R3]
SAVED = [getattr(ac, f"UC_ARM_REG_R{i}") for i in range(4, 12)]

LEGS = {
    "reloc-m4": ["--relocatable", "-t", "cortex-m4"],
    "reloc-m4f": ["--relocatable", "-t", "cortex-m4f"],
    "reloc-m7dp": ["--relocatable", "-t", "cortex-m7dp"],
    # A32 (Cortex-R5): the same direct selector, the A32 encoder; run in ARM state
    "reloc-r5": ["--relocatable", "-t", "cortex-r5"],
    "self-m4": ["-t", "cortex-m4"],
    "self-m7dp": ["-t", "cortex-m7dp"],
}

X, Y, T = "@X", "@Y", "$t"
PRODUCERS = {
    "shl_c": f"(i64.shl {X} (i64.const 31))",
    "shl_v": f"(i64.shl {X} {Y})",
    "shrs_c": f"(i64.shr_s {X} (i64.const 33))",
    "shrs_v": f"(i64.shr_s {X} {Y})",
    "shru_c": f"(i64.shr_u {X} (i64.const 7))",
    "shru_v": f"(i64.shr_u {X} {Y})",
    "rotl_c": f"(i64.rotl {X} (i64.const 40))",
    "rotl_v": f"(i64.rotl {X} {Y})",
    "rotr_c": f"(i64.rotr {X} (i64.const 12))",
    "rotr_v": f"(i64.rotr {X} {Y})",
    "add": f"(i64.add {X} {Y})",
    "sub": f"(i64.sub {X} {Y})",
    "mul": f"(i64.mul {X} {Y})",
    "and": f"(i64.and {X} {Y})",
    "or": f"(i64.or {X} {Y})",
    "xor": f"(i64.xor {X} {Y})",
    "divs": f"(i64.div_s {X} {Y})",
    "divu": f"(i64.div_u {X} {Y})",
    "rems": f"(i64.rem_s {X} {Y})",
    "remu": f"(i64.rem_u {X} {Y})",
    "clz": f"(i64.clz {X})",
    "ctz": f"(i64.ctz {X})",
    "popcnt": f"(i64.popcnt {X})",
    "const": "(i64.const 0x1122334455667788)",
    "exts": f"(i64.extend_i32_s (i32.wrap_i64 {Y}))",
    "extu": f"(i64.extend_i32_u (i32.wrap_i64 {Y}))",
    "ext8": f"(i64.extend8_s {Y})",
    "ext16": f"(i64.extend16_s {Y})",
    "ext32": f"(i64.extend32_s {Y})",
    "select": f"(select {X} {Y} (i32.wrap_i64 {Y}))",
    "gety": Y,
    "tee": f"(local.tee {T} (i64.xor {X} {Y}))",
}
K = "(i64.const 0x5a5a5a5a5a5a5a5a)"
COND = f"(i64.ne {X} (i64.const 7))"
EXITS = {
    "fall": "{p}",
    "ret": "(return {p})",
    "ifret": f"(if {COND} (then (return {{p}}))) {K}",
    "ifelse": f"(if (result i64) {COND} (then (return {{p}})) (else {K}))",
    "br0": "(br 0 {p})",
    "blkbr": f"(block (br 1 {{p}})) {K}",
    "brif": f"(drop (br_if 0 {{p}} {COND})) {K}",
    "brtable": f"(br_table 0 0 {{p}} (i32.wrap_i64 {Y}))",
    "loopret": f"(loop (return {{p}})) {K}",
    "retdead": f"(return {{p}}) {K}",
    "brdead": f"(br 0 {{p}}) {K}",
}
# x = (a << 32) | (a ^ b), y = sext(b) for the two i32-parameter signatures
N_X = ("(i64.or (i64.shl (i64.extend_i32_u (local.get $a)) (i64.const 32)) "
       "(i64.extend_i32_u (i32.xor (local.get $a) (local.get $b))))")
N_Y = "(i64.extend_i32_s (local.get $b))"
# sig -> (params, i64 locals, prologue, X, Y)
SIGS = {
    # both i64 parameters live in r0:r1 / r2:r3 — the direct selector everywhere
    "w": ("(param $x i64) (param $y i64)", "", "", "(local.get $x)", "(local.get $y)"),
    # i32 parameters rebuilt into i64 LOCALS
    "l": ("(param $a i32) (param $b i32)", "(local $x i64) (local $y i64)",
          f"(local.set $x {N_X}) (local.set $y {N_Y})", "(local.get $x)", "(local.get $y)"),
    # i32 parameters, x / y recomputed INLINE (no i64 local unless `tee`): the
    # shape the self-contained OPTIMIZED path accepts for a tail exit
    "n": ("(param $a i32) (param $b i32)", "", "", N_X, N_Y),
}

# (x, y) i64 pairs: distinct high words (the bug returns x's hi), shift counts
# straddling 32, y = 0 (div/rem trap), INT64_MIN / -1 (div_s overflow), x = 7
# (the not-taken arm of ifret/ifelse/brif).
W_VECS = [
    (0x0123456789ABCDEF, 0), (3, 31), (0x0123456789ABCDEF, 33), (-1, 5),
    (0x8000_0000_0000_0000, -1), (0xFEDCBA9876543210, 0x1_0000_0003),
    (7, 64), (0x0000_0001_0000_0000, 1), (0x7FFF_FFFF_0000_0001, 63),
]
N_VECS = [(0x01234567, 0), (3, 31), (0x01234567, 33), (-1, 5),
          (-0x80000000, -1), (0x7EDCBA98, 0x76543210), (0, 7), (1, 64)]
COMPARED_FLOOR = 50_000  # measured 52,800 (6 legs x 8,800)


def fname(sig: str, prod: str, ex: str) -> str:
    return f"{sig}_{prod}_{ex}"


def build_wat() -> tuple[str, list[str]]:
    funcs, names = [], []
    for sig, (params, locs, prologue, x, y) in SIGS.items():
        for prod, p in PRODUCERS.items():
            for ex, tmpl in EXITS.items():
                n = fname(sig, prod, ex)
                names.append(n)
                tlocal = " (local $t i64)" if prod == "tee" else ""
                body = tmpl.format(p=p).replace("@X", x).replace("@Y", y)
                funcs.append(f'(func (export "{n}") {params} (result i64) {locs}{tlocal}\n'
                             f"  {prologue} {body})")
    return "(module\n" + "\n".join(funcs) + ")\n", names


def to_s(v: int, bits: int) -> int:
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def words(sig: str, args) -> list[int]:
    if sig == "w":
        x, y = (a & M64 for a in args)
        return [x & M32, x >> 32, y & M32, y >> 32]
    return [a & M32 for a in args]


class Image:
    """A loaded object. `relocatable` maps raw `.text`; otherwise PT_LOAD
    segments are mapped and the image boots through its own Reset_Handler up
    to the entry scaffold (`blx r0`), as i64_result_pair_1189 does."""

    def __init__(self, path: Path, relocatable: bool, thumb: bool = True):
        self.thumb = thumb
        self.mu = mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
        self.trapped = False
        with path.open("rb") as fh:
            elf = ELFFile(fh)
            st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
            raw = {s.name: s["st_value"] for s in st.iter_symbols() if s.name}
            if relocatable:
                rels = [s.name for s in elf.iter_sections()
                        if s["sh_type"] in ("SHT_REL", "SHT_RELA") and s.name.startswith(".rel.text")]
                if rels:
                    sys.exit(f"relocatable object carries {rels}: the fixture must be relocation-free")
                text = elf.get_section_by_name(".text").data()
                base = 0x10000
                mu.mem_map(base, (len(text) + 0xFFFF) & ~0xFFFF)
                mu.mem_write(base, text)
                self.syms = {k: (v & ~1) + base for k, v in raw.items()}
                self.entry_bit = 1 if thumb else 0
                self.sp0 = 0x0E00_F000
                mu.mem_map(0x0E00_0000, 0x10000)
                mu.mem_map(RET & ~0xFFF, 0x1000)
                self.regs = {}
                self.snap = None
                self._seed_cpacr()
                return
            segs = [(sg["p_vaddr"], sg["p_memsz"], sg.data())
                    for sg in elf.iter_segments() if sg["p_type"] == "PT_LOAD"]
        self.syms = raw
        self.entry_bit = 1
        text_va, _, text = min(segs, key=lambda s: s[0])
        sp0, reset = struct.unpack_from("<II", text, 0)
        self.sp0 = sp0
        ram = [(va, sz) for va, sz, _ in segs if va != text_va]
        self.ram_lo = min((va for va, _ in ram), default=sp0 - 0x20000) & ~0xFFF
        self.ram_hi = (max(sp0, max((va + sz for va, sz in ram), default=0)) + 0xFFF) & ~0xFFF
        text_lo = text_va & ~0xFFF
        mu.mem_map(text_lo, ((text_va + len(text) + 0xFFF) & ~0xFFF) - text_lo)
        mu.mem_write(text_va, text)
        mu.mem_map(self.ram_lo, self.ram_hi - self.ram_lo)
        for va, _, data in segs:
            if va != text_va and data:
                mu.mem_write(va, data)
        mu.mem_map(RET & ~0xFFF, 0x1000)
        mu.mem_map(0xE000E000, 0x1000)
        trap = raw.get("Trap_Handler", 0) & ~1

        def on_trap(uc, *_):
            self.trapped = True
            uc.emu_stop()

        if trap:
            mu.hook_add(UC_HOOK_CODE, on_trap, begin=trap, end=trap + 1)
        mu.hook_add(UC_HOOK_INTR, on_trap)
        self._seed_cpacr()
        pc = reset & ~1
        while True:
            hw = struct.unpack_from("<H", text, pc - text_va)[0]
            if hw == 0x4780:  # blx r0 — the entry scaffold
                break
            pc += 4 if (hw >> 11) in (0b11101, 0b11110, 0b11111) else 2
        mu.reg_write(ac.UC_ARM_REG_SP, sp0)
        mu.emu_start(reset | 1, pc, count=BOOT_LIMIT)
        if (mu.reg_read(ac.UC_ARM_REG_PC) & ~1) != pc or self.trapped:
            sys.exit(f"boot did not reach the entry scaffold (pc={mu.reg_read(ac.UC_ARM_REG_PC):#x})")
        self.regs = {r: mu.reg_read(r) & M32 for r in (ac.UC_ARM_REG_R9, ac.UC_ARM_REG_R10, ac.UC_ARM_REG_R11)}
        self.snap = bytes(mu.mem_read(self.ram_lo, self.ram_hi - self.ram_lo))

    def _seed_cpacr(self):
        try:  # FPU on, for the hard-float targets' prologues
            self.mu.reg_write(ac.UC_ARM_REG_C1_C0_2, self.mu.reg_read(ac.UC_ARM_REG_C1_C0_2) | (0xF << 20))
            self.mu.reg_write(ac.UC_ARM_REG_FPEXC, 0x40000000)
        except UcError:
            pass

    def at_udf(self) -> bool:
        try:
            pc = self.mu.reg_read(ac.UC_ARM_REG_PC) & ~1
            hw1, hw2 = struct.unpack("<HH", bytes(self.mu.mem_read(pc, 4)))
        except UcError:
            return False
        if not self.thumb:  # A32 UDF: cond=1110 0111 1111 ... 1111
            return (hw2 >> 4) == 0xE7F and (hw1 & 0xF0) == 0xF0
        return (hw1 & 0xFF00) == 0xDE00 or ((hw1 & 0xFFF0) == 0xF7F0 and (hw2 & 0xF000) == 0xA000)

    def call(self, fn: str, ws: list[int]):
        mu = self.mu
        if self.snap is not None:
            mu.mem_write(self.ram_lo, self.snap)
        for i, r in enumerate(SAVED):
            mu.reg_write(r, 0xC5C50000 + i)
        for r, v in self.regs.items():
            mu.reg_write(r, v)
        before = {r: mu.reg_read(r) & M32 for r in SAVED}
        for i, r in enumerate(ARG_REGS):
            mu.reg_write(r, ws[i] if i < len(ws) else POISON)
        mu.reg_write(ac.UC_ARM_REG_SP, self.sp0)
        mu.reg_write(ac.UC_ARM_REG_LR, RET | 1)
        self.trapped = False
        try:
            mu.emu_start(self.syms[fn] | self.entry_bit, RET, count=CALL_LIMIT)
        except UcError as e:
            return ("trap",) if self.at_udf() else ("fault", str(e)), []
        if self.trapped:
            return ("trap",), []
        if (mu.reg_read(ac.UC_ARM_REG_PC) & ~1) != RET:
            return ("timeout",), []
        viol = [f"R{4 + i} clobbered" for i, r in enumerate(SAVED) if (mu.reg_read(r) & M32) != before[r]]
        if (mu.reg_read(ac.UC_ARM_REG_SP) & M32) != self.sp0:
            viol.append("SP imbalance")
        return ("ok", (mu.reg_read(ac.UC_ARM_REG_R0) & M32) | ((mu.reg_read(ac.UC_ARM_REG_R1) & M32) << 32)), viol


def main() -> int:
    wat, names = build_wat()
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
    ex = inst.exports(store)
    fails: list[str] = []
    compared = ok_trap = 0
    by_exit: dict[str, int] = {}
    want_cache: dict[tuple[str, tuple], int | None] = {}
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "i64ret1710.wat"
        src.write_text(wat)
        for leg, flags in LEGS.items():
            out = Path(td) / f"{leg}.o"
            r = subprocess.run([SYNTH, "compile", str(src), "--all-exports", *flags, "-o", str(out)],
                               capture_output=True, text=True)
            if r.returncode != 0:
                print(f"RESULT: FAIL — {leg} did not compile: {r.stderr[-400:]}")
                return 1
            img = Image(out, leg.startswith("reloc"), thumb=not leg.endswith("-r5"))
            missing = [n for n in names if n not in img.syms]
            if missing:
                fails.append(f"{leg}: {len(missing)} exports missing (declined?): {missing[:8]}")
            n_leg = bad_leg = 0
            for name in names:
                if name in missing:
                    continue
                sig, exit_ = name.split("_", 1)[0], name.rsplit("_", 1)[1]
                for args in (W_VECS if sig == "w" else N_VECS):
                    key = (name, args)
                    if key not in want_cache:
                        bits = 64 if sig == "w" else 32
                        try:
                            want_cache[key] = ex[name](store, *[to_s(a, bits) for a in args]) & M64
                        except wasmtime.Trap:
                            want_cache[key] = None
                    want = want_cache[key]
                    got, viol = img.call(name, words(sig, args))
                    compared += 1
                    n_leg += 1
                    if want is None:
                        if got[0] == "trap":
                            ok_trap += 1
                            continue
                        kind = f"trap-miss got={got}"
                    elif got[0] != "ok":
                        kind = f"{got[0]} {got[1:]}"
                    elif got[1] != want:
                        kind = f"mismatch want={want:#018x} got={got[1]:#018x}"
                    elif viol:
                        kind = "contract " + "; ".join(viol)
                    else:
                        continue
                    bad_leg += 1
                    by_exit[exit_] = by_exit.get(exit_, 0) + 1
                    if bad_leg <= 12:
                        fails.append(f"{leg}:{name}{args}: {kind}")
            if bad_leg > 12:
                fails.append(f"{leg}: ... {bad_leg - 12} more wrong vectors on this leg")
            print(f"  {leg}: {len(names) - len(missing)}/{len(names)} exports, "
                  f"{n_leg} vectors, {bad_leg} wrong")
    if compared < COMPARED_FLOOR:
        fails.append(f"FLOOR: only {compared} vectors compared, floor {COMPARED_FLOOR}")
    for f in fails:
        print(f"FAIL {f}")
    wrong = sum(by_exit.values())
    if by_exit:
        print("  wrong vectors by exit: " + ", ".join(f"{k}={v}" for k, v in sorted(by_exit.items())))
    print(f"#1710 I64RET CHECKS={compared - wrong}/{compared} (ok-trap {ok_trap})")
    print("RESULT: " + ("PASS" if not fails else f"FAIL ({len(fails)})"))
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
