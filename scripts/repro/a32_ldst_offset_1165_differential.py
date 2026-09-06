#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 124
"""RQ-63-ARMI64OFF (#1165) — load/store static-offset materialization oracle,
BOTH ARM ISAs, offsets straddling every immediate-field boundary.

WHAT WAS WRONG (measured on main before the fix, synth 0.62.0):

  * A32 (the `-b arm` DEFAULT with no `--target`, i.e. what the v0.62 reach
    census ran): `I64Ldr`/`I64Str` with `offset > 0xFFB` DECLINED loudly —
    46 of the 110 core-module declines. On the SAME target the word/sub-word
    immediate arms did NOT decline: `encode_mem_addr` masked `& 0xFFF` and the
    halfword/signed-byte arms masked `& 0xFF`, so `i32.load offset=5000`
    compiled to `ldr r0,[ip,#904]` and `i32.load16_u offset=256` to
    `ldrh r0,[ip]` — exit 0, wrong address. Strictly worse than the decline.
  * Thumb-2 (`--target cortex-m4`): `i64_effective_base` CLAMPED a negative
    offset (a memarg >= 2^31 after the selector's `as i32` cast) to 0, so
    `i64.load offset=0xfffffff8` read `[R11+addr]` while the i32 form of the
    same memarg materialized the full value.

THE ORACLE: the fixture (`a32_ldst_offset_1165.wat`) is compiled TWICE —
once exactly as the census did (`-b arm --all-exports --relocatable`, no
target → Arm32) and once for cortex-m4 (Thumb-2, #382's path as the
regression guard) — and the SAME call program runs under wasmtime (ground
truth) and under unicorn (UC_MODE_ARM / UC_MODE_THUMB, R11 = linear-memory
base). Every offset access is CROSS-ADDRESSED: a value stored via `offset=K`
is read back through an ABSOLUTE load at `(addr+K) mod 2^32`, and an
`offset=K` load reads a value written absolutely — a dropped, masked or
clamped offset lands somewhere else and mismatches; a self-consistent round
trip could not see it. Every case owns a distinct slot (asserted).

THE >= 2^31 CASES and the compliance envelope: `addr + 0xfffffff8` exceeds
every memory wasmtime can hold, so wasmtime TRAPS (spec OOB) — asserted here,
so the divergence is pinned rather than implied. synth's default embedded
profile emits NO bounds trap (CLAUDE.md "Compliance envelope",
SYNTH-SAFETY-BOUNDS-DEFAULT-ENVELOPE): the access hits `R11 + (addr + offset)
mod 2^32`, the same arithmetic the i32 word path and the `--safety-bounds
software` guard (which round-trips the same `as i32` cast) already use. For
those steps the expected value is that envelope formula — computed by this
harness from the value it wrote, never from the object under test — and the
width rule used for it is cross-checked against wasmtime on every
non-trapping step.

A decline (exit != 0 on the strict census-shaped compile) is a FAIL for this
oracle: the artifact's point is acceptance WITH the right value.

Run (rebuild synth first):
  python3 scripts/repro/a32_ldst_offset_1165_differential.py
  SYNTH=path/to/synth python3 scripts/repro/a32_ldst_offset_1165_differential.py
"""
import os
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = "scripts/repro/a32_ldst_offset_1165.wat"
WASM = "/tmp/a32_ldst_1165.wasm"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

M64 = (1 << 64) - 1
M32 = (1 << 32) - 1
MEM_BYTES = 2 * 65536        # (memory 2)
LIN_BASE = 0x20000000        # R11 under --relocatable (caller-provided)
CODE, STK = 0x10000, 0x30000000
RET = CODE + 0xF000          # return pad inside the CODE mapping

# The two ISAs. `a32` is EXACTLY the census invocation (no --target → Arm32);
# `thumb2` is #382's path and the regression guard for it.
LEGS = {
    "a32": {
        "args": ["-b", "arm"],
        "elf": "/tmp/a32_ldst_1165_a32.o",
        "mode": UC_MODE_ARM,
        "thumb": False,
    },
    "thumb2": {
        "args": ["-t", "cortex-m4"],
        "elf": "/tmp/a32_ldst_1165_t2.o",
        "mode": UC_MODE_THUMB,
        "thumb": True,
    },
}


def s32(v):
    v &= M32
    return v - (1 << 32) if v >= (1 << 31) else v


def s64(v):
    v &= M64
    return v - (1 << 64) if v >= (1 << 63) else v


def sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >= (1 << (bits - 1)) else v


# (kind, offset) → the exported load/store names carry the offset in decimal or
# as the hex the wat spells; the `fffffff8` cases are the >= 2^31 memargs.
def offname(off):
    return "fffffff8" if off == 0xFFFFFFF8 else str(off)


# Width rules: how a stored value reads back through each load kind. Checked
# against wasmtime on every non-trapping step (see `main`).
WIDTH = {
    "64": lambda v: v & M64,
    "32": lambda v: v & M32,
    "16u": lambda v: v & 0xFFFF,
    "16s": lambda v: sext(v, 16) & M32,
    "8s": lambda v: sext(v, 8) & M32,
    "8u": lambda v: v & 0xFF,
}
ABS = {  # kind → (absolute load, absolute store) exports
    "64": ("ld64_abs", "st64_abs"),
    "32": ("ld32_abs", "st32_abs"),
    "16u": ("ld16u_abs", "st16_abs"),
    "16s": ("ld16u_abs", "st16_abs"),
    "8s": ("ld8u_abs", "st8_abs"),
    "8u": ("ld8u_abs", "st8_abs"),
}
STORE_KIND = {"64": "64", "32": "32", "16": "16u", "8": "8u"}

# The cases. Each is (kind, offset) for a load `ld<kind>_<off>` or
# ("st", width, offset) for a store `st<width>_<off>`. Order matters only for
# slot assignment.
LOAD_CASES = [
    ("64", 4088), ("64", 4091), ("64", 4092), ("64", 4095), ("64", 4096),
    ("64", 5000), ("64", 70000), ("64", 0xFFFFFFF8),
    ("32", 4095), ("32", 4096), ("32", 5000), ("32", 0xFFFFFFF8),
    ("16u", 255), ("16u", 256), ("16s", 256), ("16u", 5000),
    ("8s", 255), ("8s", 256),
    ("8u", 4095), ("8u", 4096),
]
STORE_CASES = [
    ("64", 4088), ("64", 4092), ("64", 4096), ("64", 70000), ("64", 0xFFFFFFF8),
    ("32", 4095), ("32", 4096), ("32", 0xFFFFFFF8),
    ("16", 255), ("16", 256),
    ("8", 4096),
]


def value_for(k, kind):
    """A distinct, non-zero, sign-bit-exercising value per case."""
    if kind == "64":
        return (0x1122334455667788 + k * 0x0101010101010101) & M64 | (1 << 63)
    if kind == "32":
        return (0xC0DE0000 + k * 0x10101) & M32
    if kind in ("16u", "16s", "16"):
        return 0x8001 + k          # bit 15 set: 16s must sign-extend
    return 0x80 + k                # bit 7 set: 8s must sign-extend


def build_program():
    """Returns steps: dict(fn, args, kind, big, trap, env, env_only, label).
    `trap`: wasmtime must trap on this call (a >= 2^31 memarg). `env`: the
    width-rule expectation; with `env_only` False it is CROSS-CHECKED against
    wasmtime, with `env_only` True (the wrapped load, and the absolute read
    after a wrapped store — wasmtime never wrote it) it IS the expectation.
    Each case gets its own 64-byte-strided slot; the effective addresses are
    asserted pairwise distinct."""
    steps, effs = [], {}
    k = 0

    def slot(off):
        # addr such that addr+off is 8-aligned and distinct per case.
        a = 64 * (k + 1)
        a += (-(a + off)) % 8
        if off == 0xFFFFFFF8:
            a += 16  # keep the wrapped address inside the region (addr >= 8)
        return a

    for kind, off in LOAD_CASES:
        a = slot(off)
        eff = (a + off) & M32
        effs[("ld", kind, off)] = eff
        v = value_for(k, kind)
        ld_abs, st_abs = ABS[kind]
        big = kind == "64"
        wraps = off == 0xFFFFFFF8
        steps.append(dict(fn=st_abs, args=[eff, v], kind=None, big=big,
                          trap=False, env=None, env_only=False,
                          label=f"{st_abs}({eff:#x}, {v:#x})"))
        steps.append(dict(fn=f"ld{kind}_{offname(off)}", args=[a], kind=kind,
                          big=big, trap=wraps, env=WIDTH[kind](v), env_only=wraps,
                          label=f"ld{kind}_{offname(off)}({a:#x}) -> abs {eff:#x}"))
        k += 1
    for width, off in STORE_CASES:
        kind = STORE_KIND[width]
        a = slot(off)
        eff = (a + off) & M32
        effs[("st", width, off)] = eff
        v = value_for(k, kind)
        ld_abs, _ = ABS[kind]
        big = kind == "64"
        wraps = off == 0xFFFFFFF8
        steps.append(dict(fn=f"st{width}_{offname(off)}", args=[a, v],
                          kind=None, big=big, trap=wraps, env=None, env_only=False,
                          label=f"st{width}_{offname(off)}({a:#x}, {v:#x}) -> abs {eff:#x}"))
        steps.append(dict(fn=ld_abs, args=[eff], kind=kind, big=big,
                          trap=False, env=WIDTH[kind](v) if wraps else None,
                          env_only=wraps, label=f"{ld_abs}({eff:#x})"))
        k += 1
    # Distinct slots: a wrong address in one case must not land on another's
    # value and look right by accident.
    vals = list(effs.values())
    assert len(vals) == len(set(vals)), f"slot collision: {effs}"
    assert all(e + 8 <= MEM_BYTES for e in vals), f"slot outside memory: {effs}"
    return steps


def run_wasmtime(steps):
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    ex = inst.exports(store)
    out = []
    for st in steps:
        args = [s32(st["args"][0])]
        if len(st["args"]) > 1:
            args.append(s64(st["args"][1]) if st["big"] and st["fn"].startswith("st64")
                        else s32(st["args"][1]))
        try:
            r = ex[st["fn"]](store, *args)
        except wasmtime.Trap:
            out.append("TRAP")
            continue
        if st["kind"] is not None:
            out.append(r & (M64 if st["big"] else M32))
        else:
            out.append(None)
    return out


def compile_leg(name, leg):
    """Strict census-shaped compile: a decline is a FAIL. Returns stderr on
    failure, None on success."""
    cmd = [SYNTH, "compile", WASM, *leg["args"], "--all-exports",
           "--relocatable", "-o", leg["elf"]]
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        skipped = [ln for ln in p.stderr.splitlines()
                   if "skipping function" in ln or "were skipped" in ln]
        return "\n".join(skipped[-8:]) or p.stderr[-600:]
    return None


def load_elf(path):
    ef = ELFFile(open(path, "rb"))
    text_idx = ef.get_section_index(".text")
    syms = {s.name: s["st_value"] & ~1 for sec in ef.iter_sections()
            if sec.header.sh_type == "SHT_SYMTAB"
            for s in sec.iter_symbols()
            if s.name and s["st_shndx"] == text_idx}
    text = ef.get_section_by_name(".text")
    return text.data(), text["sh_addr"], syms


def run_unicorn(leg, steps):
    code, base, syms = load_elf(leg["elf"])
    mu = Uc(UC_ARCH_ARM, leg["mode"])
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN_BASE, MEM_BYTES)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_write(CODE, code)
    thumb = leg["thumb"]
    lr = RET | 1 if thumb else RET
    out = []
    for st in steps:
        fn = st["fn"]
        if fn not in syms:
            out.append(f"MISSING({fn})")
            continue
        mu.reg_write(UC_ARM_REG_R0, st["args"][0] & M32)
        if len(st["args"]) > 1:
            v = st["args"][1]
            if st["big"]:
                # (i32, i64): the i64 is even-aligned to R2:R3 (AAPCS, #518)
                mu.reg_write(UC_ARM_REG_R0 + 2, v & M32)
                mu.reg_write(UC_ARM_REG_R0 + 3, (v >> 32) & M32)
            else:
                mu.reg_write(UC_ARM_REG_R1, v & M32)
        mu.reg_write(UC_ARM_REG_R11, LIN_BASE)
        mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_LR, lr)
        start = CODE + syms[fn] - base
        try:
            mu.emu_start(start | 1 if thumb else start, RET, count=4000)
        except UcError as e:
            out.append(f"UCERR({fn}: {e})")
            continue
        if st["kind"] is None:
            out.append(None)
        else:
            lo = mu.reg_read(UC_ARM_REG_R0) & M32
            if st["big"]:
                hi = mu.reg_read(UC_ARM_REG_R1) & M32
                out.append((hi << 32) | lo)
            else:
                out.append(lo)
    return out


def fmt(x):
    return hex(x) if isinstance(x, int) else str(x)


def main():
    subprocess.run(["wat2wasm", WAT, "-o", WASM], check=True)
    steps = build_program()
    gt = run_wasmtime(steps)

    # Expected per step: wasmtime, except the >= 2^31 accesses, which wasmtime
    # must TRAP on (pinned) and whose expectation is the envelope formula.
    expected, rule_checked, traps_pinned = [], 0, 0
    for st, g in zip(steps, gt):
        if st["trap"]:
            # The >= 2^31 memarg: spec OOB, wasmtime MUST trap (pinned).
            assert g == "TRAP", f"{st['label']}: wasmtime did not trap ({g})"
            traps_pinned += 1
            expected.append(st["env"] if st["env_only"] else None)
            continue
        assert g != "TRAP", f"{st['label']}: unexpected wasmtime trap"
        if st["env_only"]:
            # The absolute read after a wrapped store: wasmtime never wrote
            # it, so the envelope formula is the expectation.
            expected.append(st["env"])
        elif st["env"] is not None:
            # A non-trapping offset load: the width rule the envelope steps
            # rely on must agree with wasmtime here, or those steps are
            # untrusted.
            assert g == st["env"], f"width rule drift on {st['label']}: {fmt(g)} vs {fmt(st['env'])}"
            rule_checked += 1
            expected.append(g)
        else:
            expected.append(g)
    assert rule_checked >= 15, f"width rule cross-checked on only {rule_checked} steps"
    assert traps_pinned == 4, f"expected 4 pinned wasmtime traps, saw {traps_pinned}"
    print(f"wasmtime: {len(steps)} steps; width rule cross-checked on {rule_checked} "
          f"offset loads; {traps_pinned} >= 2^31 accesses pinned as spec-OOB traps "
          f"(expected via the compliance-envelope formula on synth)")

    ok_all = True
    for name, leg in LEGS.items():
        print(f"== leg {name}: synth compile {' '.join(leg['args'])} --all-exports --relocatable")
        err = compile_leg(name, leg)
        if err is not None:
            print(f"  COMPILE DECLINED (strict census shape) <-- #1165\n{err}")
            ok_all = False
            # Still run what compiled, so the transcript shows the values.
            cmd = [SYNTH, "compile", WASM, *leg["args"], "--all-exports",
                   "--relocatable", "--allow-skipped-exports", "-o", leg["elf"]]
            if subprocess.run(cmd, capture_output=True).returncode != 0:
                print("  (partial compile also failed; leg skipped)")
                continue
        got = run_unicorn(leg, steps)
        bad = 0
        for st, e, g in zip(steps, expected, got):
            if st["kind"] is None and not isinstance(g, str):
                continue  # a store: checked through the following abs read
            if g != e:
                bad += 1
                print(f"  MISMATCH {st['label']}: expected {fmt(e)}, got {fmt(g)}")
        checked = sum(1 for st in steps if st["kind"] is not None)
        print(f"  {checked - bad}/{checked} values match")
        ok_all &= bad == 0
    print("ORACLE: PASS" if ok_all else "ORACLE: FAIL  <-- #1165")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
