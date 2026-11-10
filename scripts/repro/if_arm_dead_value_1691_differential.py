#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 1392
"""RQ-91-O2FLOAT (#1691) — an `if` arm that ends in an unconditional transfer,
EXECUTED on every ARM rung against wasmtime.

THE DEFECT. The direct selector (`select_with_stack`, the only ARM selector)
keeps a simulated operand stack. A value-carrying `br` lands its value in the
target join but leaves it ON that stack (it is peeked, not popped — the dead
code after a transfer may still read it). #1215 discards such leftovers at a
plain block's `end`, but an `if` arm's end never did: an else-less if dropped
nothing, and an if/else whose arms left different counts published the dead
arm's values beside the live arm's results. The code after the if then read a
dead arm's register instead of the value beneath the if. cpetig's `wasm-opt
-O2` flight controller returned motors ~1e-3 off, exit 0, no warning — at f32,
but the class is not float-specific: the i32 twin returns 0 for 99.

THE FIXTURE (`if_arm_dead_value_1691.wat`). Each `t_*` export puts a value
beneath the if and consumes it after: then-arm br, else-arm br, both arms dead,
br from a nested block, br_table, unreachable, return leaving an operand
behind, a carried value unwound into a void block, mismatched arm counts at a
result-typed if/else (dead then, dead else, both dead), the labels.wast loop
exit with a value beneath, at i32, i64, f32 and f64. `ctl_*` exports are
CONTROLS (a dead arm that left exactly the if's arity; no dead arm): they
execute correctly before the fix too, so a red here is the fix's own
regression. `refuse_below` is the LOUD-REFUSAL pin: its dead code drops below
the if's entry height, which the stack model cannot recover, so every leg must
skip it with the #1691 decline.

THE LEGS. cortex-m4f, cortex-m7 (single-precision VFP) and cortex-m7dp
(double), each `--relocatable` and as the self-contained image; cortex-r5 (A32)
relocatable and image, integer exports only (no FPU: its float exports are
declined by GI-FPU-002 and must be). f64 exports run on cortex-m7dp only.
Every leg's compiled set is checked EXACTLY against that rule, so a newly
declined export is red, never a smaller denominator.

EXECUTION. Each compiled export is called with x in {0, 1, 5, 7} in two machine
states (all caller-saved core and S registers zeroed, and filled from a seeded
RNG), under unicorn, and compared BIT-EXACT with wasmtime: same value, or a
trap on both sides (a `udf`). The floor below is DERIVED from the leg rules
and checked against the header before anything runs (#1331).

RED on 0d22bafe: the `t_*` exports return the dead arm's values and
`refuse_below` compiles. GREEN after -> RESULT: PASS.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH_BIN=./target/debug/synth python3 scripts/oracle_run.py \\
      scripts/repro/if_arm_dead_value_1691_differential.py
"""
import os
import random
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as A

HERE = Path(__file__).resolve().parent
WAT = HERE / "if_arm_dead_value_1691.wat"
SYNTH = os.environ.get("SYNTH_BIN") or os.environ.get("SYNTH", "./target/debug/synth")

XS = (0, 1, 5, 7)
STATES = ("zeroed", "garbage")
REFUSE = "refuse_below"
REFUSE_TEXT = "#1691: unreachable code after a br/br_table/return/unreachable"

# (leg, synth flags, thumb, fpu) — fpu: None, "sp" or "dp".
LEGS = [
    ("m4f-reloc", ["--target", "cortex-m4f", "--relocatable"], True, "sp"),
    ("m4f-image", ["--target", "cortex-m4f"], True, "sp"),
    ("m7-reloc", ["--target", "cortex-m7", "--relocatable"], True, "sp"),
    ("m7-image", ["--target", "cortex-m7"], True, "sp"),
    ("m7dp-reloc", ["--target", "cortex-m7dp", "--relocatable"], True, "dp"),
    ("m7dp-image", ["--target", "cortex-m7dp"], True, "dp"),
    ("r5-reloc", ["--target", "cortex-r5", "--relocatable"], False, None),
    ("r5-image", ["--target", "cortex-r5"], False, None),
]

RET = 0x0F00_0000
STACK, STACK_SIZE = 0x4000_0000, 0x1_0000
SP0 = STACK + STACK_SIZE - 0x100
SCRATCH = 0x3000_0000  # R9/R10/R11 point here; no fixture touches memory


def exports():
    """[(name, result valtype)] from wasmtime's own view of the module."""
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_text())
    out = []
    for e in mod.exports:
        res = e.type.results
        out.append((e.name, str(res[0]) if res else None))
    return out


def runs_on(result, fpu):
    if result == "f32":
        return fpu in ("sp", "dp")
    if result == "f64":
        return fpu == "dp"
    return True


def expected_emulations():
    """Derived from the leg rules: every runnable non-refusal export, every x,
    every machine state, on every leg."""
    ex = exports()
    n = 0
    for _, _, _, fpu in LEGS:
        n += sum(1 for name, r in ex if name != REFUSE and runs_on(r, fpu))
    return n * len(XS) * len(STATES)


def declared_floor():
    src = Path(__file__).read_text()
    m = re.search(r"^# ci-checks: emulations >= (\d+)$", src, re.M)
    if not m:
        sys.exit("REFUSE: no `# ci-checks: emulations >= N` header in this file")
    return int(m.group(1))


def reference(ex):
    """{(name, x): ('ok', bits) | ('trap',)} from wasmtime."""
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_text())
    out = {}
    for name, r in ex:
        for x in XS:
            store = wasmtime.Store(eng)
            inst = wasmtime.Instance(store, mod, [])
            try:
                v = inst.exports(store)[name](store, x)
            except wasmtime.Trap:
                out[(name, x)] = ("trap",)
                continue
            if r == "f32":
                bits = struct.unpack("<I", struct.pack("<f", v))[0]
            elif r == "f64":
                bits = struct.unpack("<Q", struct.pack("<d", v))[0]
            elif r == "i64":
                bits = v & 0xFFFF_FFFF_FFFF_FFFF
            else:
                bits = v & 0xFFFF_FFFF
            out[(name, x)] = ("ok", bits)
    return out


def compile_leg(flags, tmp, leg):
    out = os.path.join(tmp, f"{leg}.elf")
    r = subprocess.run([SYNTH, "compile", str(WAT), *flags, "--all-exports",
                        "--allow-skipped-exports", "-o", out],
                       capture_output=True, text=True)
    text = r.stdout + r.stderr
    skipped = dict(re.findall(r"skipping function '([^']+)': (.*)", text))
    return r.returncode, out, skipped, text


class Image:
    def __init__(self, path, thumb):
        self.thumb = thumb
        with open(path, "rb") as fh:
            ef = ELFFile(fh)
            self.syms = {}
            for sec in ef.iter_sections():
                if sec["sh_type"] == "SHT_SYMTAB":
                    for s in sec.iter_symbols():
                        if s.name:
                            self.syms[s.name] = s["st_value"]
            self.secs = [(s["sh_addr"], s.data()) for s in ef.iter_sections()
                         if s["sh_flags"] & 2 and s["sh_type"] == "SHT_PROGBITS"]
        self.uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
        pages = set()
        for a, d in self.secs:
            for p in range(a & ~0xFFF, a + max(len(d), 1), 0x1000):
                pages.add(p)
        for p in sorted(pages):
            self.uc.mem_map(p, 0x1000)
        for a, d in self.secs:
            self.uc.mem_write(a, d)
        for base, size in ((RET, 0x1000), (STACK, STACK_SIZE), (SCRATCH, 0x1000)):
            self.uc.mem_map(base, size)

    def is_udf(self, pc):
        try:
            if self.thumb:
                hw = struct.unpack("<H", bytes(self.uc.mem_read(pc, 2)))[0]
                return hw & 0xFF00 == 0xDE00
            w = struct.unpack("<I", bytes(self.uc.mem_read(pc, 4)))[0]
            return w & 0xFFF000F0 == 0xE7F000F0
        except UcError:
            return False

    def call(self, name, result, x, rng):
        uc = self.uc
        pick = (lambda: rng.getrandbits(32)) if rng else (lambda: 0)
        if self.thumb:
            uc.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)
            uc.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)
            for i in range(16):
                uc.reg_write(getattr(A, f"UC_ARM_REG_S{i}"), pick())
        for i in (1, 2, 3, 12):
            uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), pick())
        for i in (9, 10, 11):
            uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), SCRATCH)
        uc.reg_write(A.UC_ARM_REG_R0, x)
        uc.reg_write(A.UC_ARM_REG_SP, SP0)
        uc.reg_write(A.UC_ARM_REG_LR, RET | (1 if self.thumb else 0))
        entry = self.syms[name] & ~1
        try:
            uc.emu_start(entry | (1 if self.thumb else 0), RET, count=100_000)
        except UcError as e:
            pc = uc.reg_read(A.UC_ARM_REG_PC) & ~1
            return ("trap",) if self.is_udf(pc) else ("fault", f"{e} at {pc:#x}")
        if uc.reg_read(A.UC_ARM_REG_PC) & ~1 != RET:
            return ("fault", "did not return")
        if result == "f32":
            return ("ok", uc.reg_read(A.UC_ARM_REG_S0) & 0xFFFF_FFFF)
        if result == "f64":
            return ("ok", uc.reg_read(A.UC_ARM_REG_D0) & 0xFFFF_FFFF_FFFF_FFFF)
        lo = uc.reg_read(A.UC_ARM_REG_R0) & 0xFFFF_FFFF
        if result == "i64":
            return ("ok", lo | (uc.reg_read(A.UC_ARM_REG_R1) & 0xFFFF_FFFF) << 32)
        return ("ok", lo)


def main():
    want, got = expected_emulations(), declared_floor()
    if want != got:
        sys.exit(f"REFUSE: the declared floor is `emulations >= {got}` but the leg "
                 f"rules derive {want} — fix the header, not the rules")
    ex = exports()
    ref = reference(ex)
    failures = []
    emulations = 0
    per_leg = {}
    per_export = {}
    with tempfile.TemporaryDirectory(prefix="o2float1691_") as tmp:
        for leg, flags, thumb, fpu in LEGS:
            rc, path, skipped, text = compile_leg(flags, tmp, leg)
            if rc != 0:
                failures.append(f"{leg}: compile rc={rc}: {text.strip().splitlines()[-1:]}")
                continue
            expect_run = {n for n, r in ex if n != REFUSE and runs_on(r, fpu)}
            expect_skip = {n for n, _ in ex} - expect_run
            if set(skipped) != expect_skip:
                failures.append(f"{leg}: skipped {sorted(set(skipped) ^ expect_skip)} "
                                f"differs from the leg rule")
            why = skipped.get(REFUSE, "")
            if REFUSE_TEXT not in why:
                failures.append(f"{leg}: {REFUSE} not declined with the #1691 "
                                f"below-entry refusal (got: {why[:100]!r})")
            img = Image(path, thumb)
            bad = 0
            for name, r in ex:
                if name not in expect_run or name not in img.syms:
                    continue
                for state in STATES:
                    rng = random.Random(f"{leg}:{name}:{state}") if state == "garbage" else None
                    for x in XS:
                        g = img.call(name, r, x, rng)
                        emulations += 1
                        w = ref[(name, x)]
                        if g != w:
                            bad += 1
                            per_export[name] = per_export.get(name, 0) + 1
                            failures.append(f"{leg} {state} {name}({x}): ARM {g}, "
                                            f"wasmtime {w}")
            per_leg[leg] = bad
    for leg, bad in per_leg.items():
        print(f"  {leg:11s} disagreeing calls: {bad}")
    if per_export:
        print("  disagreeing calls per export: " + ", ".join(
            f"{n} {c}" for n, c in sorted(per_export.items())))
    for f in failures[:40]:
        print("FAIL:", f)
    if len(failures) > 40:
        print(f"... and {len(failures) - 40} more")
    print(f"if-arm-dead-value: {emulations} emulation(s), {len(failures)} failure(s), "
          f"floor {got}")
    ok = not failures and emulations >= got
    print("RESULT: PASS" if ok else "RESULT: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
