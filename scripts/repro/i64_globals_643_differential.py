#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 28
"""#643 — i64 global.set/global.get pair correctness on BOTH ARM selectors.

Differential oracle for issue #643: on Thumb-2, an i64 global was stored/loaded
as ONE 32-bit word at [r9,#idx*4] — the high word silently dropped — and the
4-byte slot layout left no room for the second word (so a fix must ALSO shift
the offsets of every later global: the i32-after-i64 canary).

Runs the in-tree fixture `i64_globals_643.wat` on BOTH lowering paths:

  * OPTIMIZED  (`synth compile ... --target cortex-m3`)  — the IR path (the
    #643 pre-gate must route global-touching functions of a wide-global module
    to the direct selector).
  * DIRECT     (`... --relocatable`)                     — `select_with_stack`
    (the pair store/load lowering itself).

Globals are STATEFUL: one unicorn instance per path with R9 pointed at a
zeroed scratch region, exports called in sequence, results compared against
the SAME stateful sequence on one wasmtime instance:

  set32(canary); get32
  for v in {0x123456789ABCDEF0, -1, 0x8000000000000000}: set64; get_lo; get_hi
  get32                      # canary survived the i64 sets (layout-shift gate)
  roundtrip_hi(0,0)          # gale's exact repro: must be 0x12345678

Also checks the RV32 contract: the RISC-V selector has NO global lowering, so
every global-touching export must LOUD-SKIP (warn + absent from the symtab),
never silently truncate; the global-free control must still be emitted.

RQ-59-GLOBALINIT (#1052) — why this harness was STRENGTHENED: its original
fixture's initializers are all zero, and the zeroed scratch region it maps is
therefore indistinguishable from an object whose initializers were silently
DROPPED. Exactly that bug shipped: the plain relocatable path discarded every
nonzero global initializer (0x2A appeared nowhere in the ELF) and this harness
stayed green over it for its entire existence — a checker encoding a weaker
property than the one that matters (the #1055/#1054 family). The
`check_nonzero_init_contract_1052` section closes the hole with the
NONZERO-init fixture `globals_init_1052.wat`:

  1. plain `--relocatable` compile must now REFUSE loudly (non-zero exit, a
     reason naming the global initializers, #1052) — on the pre-fix compiler
     this step reds (it compiled exit-0);
  2. with `--embedder-global-init` (the explicit acknowledgment that the
     embedder evaluates initializers and seeds the R9 table) the compile
     succeeds, the harness SEEDS the table from the module's own values (read
     back through wasmtime's exported globals — the served-image-vs-runtime-
     image shape of VCR-VER-003, not a second hardcoded copy) and the
     execution differential must agree with wasmtime;
  3. the SAME object on a ZEROED table must DIVERGE from wasmtime — the
     non-vacuity anchor proving this fixture can distinguish "initializers
     written" from "initializers were all zero anyway". If step 3 ever stops
     diverging, the fixture has gone vacuous and the harness fails.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/synthvenv/bin/python \
      scripts/repro/i64_globals_643_differential.py
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R9,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("i64_globals_643.wat")
WAT_1052 = Path(__file__).with_name("globals_init_1052.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET, R11, GLOB = 0x100000, 0x900000, 0x300000, 0x20000000, 0x400000

CANARY = 0x0C0FFEE1
I64_VALUES = [0x123456789ABCDEF0, 0xFFFFFFFFFFFFFFFF, 0x8000000000000000]

# every global-touching export (must all loud-skip on RV32)
GLOBAL_FNS = ["set64", "get_lo", "get_hi", "set32", "get32", "roundtrip_hi"]


def compile_synth(out, backend_args):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "--all-exports", "--allow-skipped-exports"] + backend_args
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed ({backend_args}): {r.stderr}")
    return r.stderr


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


class ArmRunner:
    """One persistent unicorn instance per path — globals live at R9=GLOB and
    must survive across calls (set-then-get ACROSS calls is the point)."""

    def __init__(self, code, base, syms, glob_seed=b""):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(CODE, 0x20000)
        self.mu.mem_map(STK - 0x10000, 0x20000)
        self.mu.mem_map(RET & ~0xFFF, 0x1000)
        # Zeroed globals table — correct for the #643 fixture ONLY because its
        # inits ARE 0. That parenthetical was load-bearing: a nonzero init
        # silently dropped by the compiler is indistinguishable from a zeroed
        # table here, which is how #1052 stayed green. The #1052 section below
        # passes `glob_seed` (the embedder-evaluated initializer image) — and
        # separately PROVES a zeroed table diverges on the nonzero fixture.
        self.mu.mem_map(GLOB, 0x1000)
        if glob_seed:
            self.mu.mem_write(GLOB, glob_seed)
        self.mu.mem_map(R11, 0x10000)
        self.mu.mem_write(CODE, code)

    def call(self, fn, args=()):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
        foff = (faddr & ~1) - self.base
        for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
            self.mu.reg_write(reg, val & 0xFFFFFFFF)
        self.mu.reg_write(UC_ARM_REG_SP, STK)
        self.mu.reg_write(UC_ARM_REG_R9, GLOB)
        self.mu.reg_write(UC_ARM_REG_R11, R11)
        self.mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            self.mu.emu_start((CODE + foff) | 1, RET, count=100000)
        except UcError as e:
            return f"ERR:{e}"
        return self.mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


class WasmtimeRunner:
    """Stateful ground truth: ONE instance for the whole sequence."""

    def __init__(self):
        engine = wasmtime.Engine()
        module = wasmtime.Module.from_file(engine, str(WAT))
        self.store = wasmtime.Store(engine)
        self.inst = wasmtime.Instance(self.store, module, [])

    def call(self, fn, args=()):
        signed = [a - (1 << 32) if a >= (1 << 31) else a for a in args]
        r = self.inst.exports(self.store)[fn](self.store, *signed)
        return (r if r is not None else 0) & 0xFFFFFFFF


def sequence(run):
    """The stateful call sequence; yields (label, fn, args)."""
    yield ("canary-set", "set32", (CANARY,))
    yield ("canary-get", "get32", ())
    for v in I64_VALUES:
        lo, hi = v & 0xFFFFFFFF, (v >> 32) & 0xFFFFFFFF
        yield (f"set64({v:#x})", "set64", (lo, hi))
        yield (f"get_lo({v:#x})", "get_lo", ())
        yield (f"get_hi({v:#x})", "get_hi", ())
    yield ("canary-survives-i64-sets", "get32", ())
    yield ("gale-roundtrip_hi", "roundtrip_hi", (0, 0))
    yield ("control-pure_add", "pure_add", (41, 1))


def run_arm_path(label, relocatable):
    out = f"/tmp/i64g643_{'rel' if relocatable else 'opt'}.o"
    args = ["-b", "arm", "--target", "cortex-m3"]
    if relocatable:
        args.append("--relocatable")
    compile_synth(out, args)
    code, base, syms = load(out)
    arm = ArmRunner(code, base, syms)
    gt = WasmtimeRunner()
    print(f"\n=== {label} path ===")
    fails = 0
    for step, fn, fargs in sequence(arm):
        exp = gt.call(fn, fargs)
        got = arm.call(fn, fargs)
        # setters return nothing; only compare value-producing steps
        is_get = fn not in ("set64", "set32")
        if not is_get:
            if isinstance(got, str):
                fails += 1
                print(f"  [BUG] {step}: {got}")
            continue
        match = got == exp
        if not match:
            fails += 1
        print(f"  [{'ok ' if match else 'BUG'}] {step}: {fn}{fargs} -> "
              f"{got if isinstance(got, str) else hex(got)}  (wasmtime {exp:#x})")
    return fails


def check_rv32_loudskip():
    """RV32 has no global lowering: global-touching exports must loud-skip
    (warn + absent symbol); the global-free control must be emitted."""
    out = "/tmp/i64g643_rv32.o"
    stderr = compile_synth(out, ["-b", "riscv"])
    _, _, syms = load(out)
    print("\n=== RV32 contract (loud-skip, not silent truncation) ===")
    fails = 0
    for fn in GLOBAL_FNS:
        skipped = fn not in syms
        warned = fn in stderr
        ok = skipped and warned
        if not ok:
            fails += 1
        print(f"  [{'ok ' if ok else 'BUG'}] {fn}: "
              f"{'loud-skipped' if skipped else 'EMITTED (silent gap?)'}"
              f"{'' if warned else ' (no warning in stderr)'}")
    if "pure_add" in syms:
        print("  [ok ] pure_add emitted (non-vacuity)")
    else:
        fails += 1
        print("  [BUG] pure_add missing — skip contract is vacuous")
    return fails


def check_nonzero_init_contract_1052():
    """RQ-59-GLOBALINIT (#1052): the nonzero-initializer contract on the plain
    relocatable path — the property the zeroed-scratch protocol above could
    never observe. Three legs, each with teeth:

      refusal    — plain --relocatable on the nonzero fixture must EXIT
                   NON-ZERO naming the global initializers (pre-fix: exit 0);
      contract   — with --embedder-global-init the compile succeeds and THIS
                   HARNESS acts as the acknowledged embedder: it seeds the R9
                   table from the module's own initial values (read back via
                   wasmtime's exported globals, #643 summed-width layout) and
                   the execution differential must agree with wasmtime;
      non-vacuity— the SAME object on a ZEROED table must DIVERGE from
                   wasmtime. If it ever stops diverging, this fixture can no
                   longer distinguish "inits written" from "inits were zero
                   anyway" and the harness fails itself.
    """
    import struct

    print("\n=== #1052 nonzero-initializer contract (plain --relocatable) ===")
    fails = 0
    env = {"PATH": "/usr/bin:/bin"}
    base_cmd = [SYNTH, "compile", str(WAT_1052), "--all-exports",
                "-b", "arm", "--target", "cortex-m3", "--relocatable"]

    # Leg 1: the refusal. Deliberately NOT "the init value is absent from the
    # object" — that was true on the broken behaviour too.
    out = "/tmp/gi1052_refuse.o"
    r = subprocess.run(base_cmd + ["-o", out], capture_output=True, text=True, env=env)
    refused = r.returncode != 0
    named = "global initializer" in r.stderr and "#1052" in r.stderr
    ok = refused and named
    if not ok:
        fails += 1
    print(f"  [{'ok ' if ok else 'BUG'}] refusal: exit={r.returncode} "
          f"{'names the global initializers' if named else 'reason missing/unnamed'}"
          f"{' (SILENT-DROP: compiled exit 0)' if not refused else ''}")

    # Leg 2: the acknowledged contract. Ground truth for the seed comes from
    # the MODULE (wasmtime-evaluated exported globals), not a second copy.
    out = "/tmp/gi1052_ack.o"
    r = subprocess.run(base_cmd + ["--embedder-global-init", "-o", out],
                       capture_output=True, text=True, env=env)
    if r.returncode != 0:
        print(f"  [BUG] --embedder-global-init compile failed: {r.stderr.splitlines()[-1] if r.stderr else r.returncode}")
        return fails + 1

    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT_1052))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = inst.exports(store)
    init_a = exports["g_a"].value(store) & 0xFFFFFFFF
    init_b = exports["g_b"].value(store) & 0xFFFFFFFFFFFFFFFF
    # #643 summed-width layout: global 0 (i32) at +0, global 1 (i64) at +4
    # (lo word first) — the contract the embedder-seeded table must follow.
    seed = struct.pack("<I", init_a) + struct.pack("<Q", init_b)

    code, base, syms = load(out)
    arm = ArmRunner(code, base, syms, glob_seed=seed)

    def gt(fn):
        v = exports[fn](store)
        return (v if v is not None else 0) & 0xFFFFFFFF

    for fn in ("get_a", "get_b_lo", "get_b_hi"):
        exp, got = gt(fn), arm.call(fn)
        ok = got == exp
        if not ok:
            fails += 1
        print(f"  [{'ok ' if ok else 'BUG'}] seeded-table {fn} -> "
              f"{got if isinstance(got, str) else hex(got)} (wasmtime {exp:#x})")

    # Leg 3: non-vacuity — the zeroed table (the old protocol) must DIVERGE.
    arm0 = ArmRunner(code, base, syms)
    got0 = arm0.call("get_a")
    diverges = got0 != gt("get_a")
    if not diverges:
        fails += 1
    print(f"  [{'ok ' if diverges else 'BUG'}] zeroed-table get_a -> "
          f"{got0 if isinstance(got0, str) else hex(got0)} "
          f"{'DIVERGES from wasmtime (fixture has teeth)' if diverges else 'agrees — fixture is VACUOUS'}")
    return fails


def main():
    total = 0
    total += run_arm_path("OPTIMIZED (default)", relocatable=False)
    total += run_arm_path("DIRECT (--relocatable)", relocatable=True)
    total += check_rv32_loudskip()
    total += check_nonzero_init_contract_1052()
    print(f"\nORACLE: {'PASS' if total == 0 else f'FAIL ({total} divergences)'}")
    sys.exit(0 if total == 0 else 1)


if __name__ == "__main__":
    main()
