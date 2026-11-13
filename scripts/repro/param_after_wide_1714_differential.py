#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 4614
"""#1714 — a narrow param that FOLLOWS a wide (or VFP-homed) param, EXECUTED
on ARM and RV32 against wasmtime.

THE DEFECT, ARM. The direct selector (`select_with_stack`, which every
wide-param function reaches, `--relocatable` or self-contained) homes params
by the width-aware AAPCS walk (`aapcs_param_layout`): an i64/f64 takes an
even-aligned core PAIR, and under AAPCS-VFP an f32/f64 takes no core register
at all. `local.get` read that home, but the narrow `local.set`/`local.tee` arm
wrote `index_to_reg(local_idx)` — the sequential register — and re-pointed the
home there. `(i64 i32)`: the i32 lives in R2, the write went to R1 (the i64's
high half) and a loop header already emitted against R2 never saw it, so the
countdown loop never ended. `(f32 i32 i32)` on a VFP target: local 1 lives in
R0, the write went to R1 — local 2.

THE DEFECT, RV32. The selector mapped param `k` to `a(k)` and refused an i64
param only when the ACCESSED param was body-inferred i64. The ilp32 psABI
passes a 2xXLEN scalar in the next TWO a-registers (no even alignment), so the
i32 of `(i64 i32)` arrives in a2 and was read from a1, the i64's high word:
`f(0, 2)` returned 0, silently.

THE FIX. ARM writes the AAPCS home (`narrow_param_home`). RV32 builds the
psABI homes from the DECLARED widths (`rv32_param_homes`): a narrow param in
a register reads/writes that register; a wide param (the #312 boundary — its
pair is not modeled) and a narrow param the psABI passes on the stack are
refused LOUDLY. So on RV32 every export that touches a wide or stack-passed
param must be declined, and every other export must compile and agree.

THE FIXTURE is generated here (no .wat enters scripts/repro/, so no corpus
census moves). For each signature in SIGS, for each narrow param k that has a
wide or float param before it, five shapes:
  g_  read k, fold the other narrow params in;
  s_  local.set k from k, then fold every narrow param (k and its neighbours);
  t_  local.tee k, same fold;
  l_  the #1714 countdown loop on k (its header reads k before any write;
      k is masked to 0..7 inside the loop so it ends), then fold;
  c_  local.set k, call an in-module identity function, then fold (a call
      frame-backs the params: the prologue must store each from its TRUE home);
  w_  local.set k, then fold EVERY param, wide ones included (catches a write
      that landed in an i64's high half).
CONTROLS: all-narrow signatures (`(i32 i32)`, `(i32 i32 i32)`) under the same
shapes, which were correct before the fix and must stay so.

THE LEGS. ARM: cortex-m4 and cortex-m7dp, `--relocatable` and self-contained
image, plus cortex-r5 (A32) relocatable and image. RV32: riscv32imac
`--relocatable`. Every compiled export is run with three argument vectors in
two machine states (unused core/VFP/arg registers zeroed, and filled with a
seeded RNG) under unicorn; args are marshalled per AAPCS(-VFP) / ilp32. The
compiled set of every leg is checked EXACTLY against its rule: ARM soft-float
legs decline any f32/f64 signature with a float op and any f32 param; RV32
declines exactly the exports that touch a non-register param (derived here
from an independent ilp32 walk).

RED on main 332a22db (see the PR for the paste). GREEN after -> RESULT: PASS.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH_BIN=./target/debug/synth python3 scripts/oracle_run.py \\
      scripts/repro/param_after_wide_1714_differential.py
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
from unicorn import (UC_ARCH_ARM, UC_ARCH_RISCV, UC_MODE_ARM, UC_MODE_RISCV32,
                     UC_MODE_THUMB, Uc, UcError)
from unicorn import arm_const as A
from unicorn import riscv_const as RV

SYNTH = os.environ.get("SYNTH_BIN") or os.environ.get("SYNTH", "./target/debug/synth")

M32, M64 = 0xFFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF
WIDE = ("i64", "f64")

# Signatures under test. Every one has at least one narrow param AFTER a wide
# or a float param, except the CONTROLS.
SIGS = [
    ("i64", "i32"),                     # the #1714 repro: i32 in R2 / a2
    ("i64", "i32", "i32"),              # R2, R3 / a2, a3
    ("i32", "i64", "i32"),              # ARM: stack (C.5) / RV32: a3
    ("i64", "i64", "i32"),              # ARM: stack / RV32: a4
    ("i32", "i64", "i32", "i32", "i32"),
    ("f64", "i32"),                     # m7dp: D0 + R0; soft: R0:R1 + R2
    ("f64", "i32", "i32"),
    ("f32", "i32", "i32"),              # VFP: S0, R0, R1 (local 1 -> R1 was local 2)
    ("f32", "f64", "i32", "f32", "i32"),
    ("i32",) * 7 + ("i64", "i32"),      # RV32: i64 split a7/stack, i32 on stack
    ("f32",) * 4 + ("i32",),            # VFP: param 4 is in R0 (index >= 4)
    ("f32",) * 5 + ("i32", "i32"),      # VFP: params 5, 6 in R0, R1
]
CONTROLS = [("i32", "i32"), ("i32", "i32", "i32")]
SHAPES = ("g", "s", "t", "l", "c", "w")

# (leg, backend, synth flags, mode, fpu) — fpu None / "dp".
LEGS = [
    ("m4-reloc", "arm", ["--target", "cortex-m4", "--relocatable"], "thumb", None),
    ("m4-image", "arm", ["--target", "cortex-m4"], "thumb", None),
    ("m7dp-reloc", "arm", ["--target", "cortex-m7dp", "--relocatable"], "thumb", "dp"),
    ("m7dp-image", "arm", ["--target", "cortex-m7dp"], "thumb", "dp"),
    ("r5-reloc", "arm", ["--target", "cortex-r5", "--relocatable"], "arm", None),
    ("r5-image", "arm", ["--target", "cortex-r5"], "arm", None),
    ("rv32-reloc", "riscv", ["-b", "riscv", "--target", "riscv32imac", "--relocatable"],
     "rv32", None),
]
STATES = ("zeroed", "garbage")
NVEC = 3

RET = 0x0F00_0000
STACK, STACK_SIZE = 0x4000_0000, 0x1_0000
SP0 = STACK + STACK_SIZE - 0x400  # stack args live ABOVE the entry SP
SCRATCH = 0x3000_0000


# ── fixture ──────────────────────────────────────────────────────────────────

def fold(j, t):
    """wasm that pushes param j folded to one i32."""
    if t == "i32":
        return f"(local.get {j})"
    if t == "f32":
        return f"(i32.reinterpret_f32 (local.get {j}))"
    v = f"(local.get {j})" if t == "i64" else f"(i64.reinterpret_f64 (local.get {j}))"
    return f"(i32.xor (i32.wrap_i64 {v}) (i32.wrap_i64 (i64.shr_u {v} (i64.const 32))))"


def mix(sig, k, wide_too):
    """i32 = k's value, multiplied and xored with every other included param
    (an FNV-style fold: every param moves the result, and RV32 has `mul` but
    no `rotl`)."""
    acc = f"(i32.mul (local.get {k}) (i32.const 0x9E3779B1))"
    for j, t in enumerate(sig):
        if j == k or (t in WIDE and not wide_too) or (t == "f32" and not wide_too):
            continue
        acc = f"(i32.xor (i32.mul {acc} (i32.const {0x01000193 + 2 * j})) {fold(j, t)})"
    return acc


def body(shape, sig, k):
    narrow = mix(sig, k, False)
    if shape == "g":
        return narrow
    if shape == "s":
        return (f"(local.set {k} (i32.add (local.get {k}) (i32.const 0x44)))\n    "
                + narrow)
    if shape == "t":
        return (f"(i32.add (local.tee {k} (i32.mul (local.get {k}) (i32.const 7))) "
                f"{narrow})")
    if shape == "l":
        # The issue's loop: the header reads k BEFORE any write (so against
        # its true home), the body writes it. Masked so it ends in <= 8 trips.
        m = f"(i32.and (local.get {k}) (i32.const 7))"
        return (f"(block (loop (br_if 1 (i32.eqz {m}))\n      "
                f"(local.set {k} (i32.sub {m} (i32.const 1))) (br 0)))\n    "
                + narrow)
    if shape == "c":
        # A call makes the direct selector frame-back every param it reads
        # (#204) and RV32 spill it to a slot (#882): the slot must be stored
        # from the param's TRUE home in the prologue.
        return (f"(local.set {k} (i32.add (local.get {k}) (i32.const 0x44)))\n    "
                f"(i32.add (call $id (local.get {k})) {narrow})")
    assert shape == "w"
    return (f"(local.set {k} (i32.xor (local.get {k}) (i32.const 0x5A5A5A5A)))\n    "
            + mix(sig, k, True))


def sig_tag(sig):
    return "".join({"i32": "i", "i64": "I", "f32": "f", "f64": "F"}[t] for t in sig)


def build_fixture():
    """[(export, sig, k, shape)] and the module text."""
    funcs = []
    out = ["(module", '  (func $id (export "id") (param i32) (result i32) (local.get 0))']
    for sig in SIGS + CONTROLS:
        for k, t in enumerate(sig):
            if t != "i32":
                continue
            if sig in SIGS and not any(u != "i32" for u in sig[:k]):
                continue  # nothing wide/float before it: not this class
            for shape in SHAPES:
                if shape == "w" and sig in CONTROLS:
                    continue
                name = f"{shape}_{sig_tag(sig)}_{k}"
                params = " ".join(sig)
                out.append(f'  (func (export "{name}") (param {params}) (result i32)\n'
                           f"    {body(shape, sig, k)})")
                funcs.append((name, sig, k, shape))
    out.append(")")
    return funcs, "\n".join(out)


# ── leg rules (exact compiled sets) ──────────────────────────────────────────

def rv32_homes(sig):
    """Independent ilp32 walk: 'reg' / 'wide' / 'stack' per param."""
    n, homes = 0, []
    for t in sig:
        if t in WIDE:
            homes.append("wide")
            n = min(n + 2, 8)
        elif n < 8:
            homes.append(("reg", n))
            n += 1
        else:
            homes.append("stack")
    return homes


def touched(sig, k, shape):
    if shape == "w":
        return set(range(len(sig)))
    return {k} | {j for j, t in enumerate(sig) if t == "i32"}


def expect_compiled(leg, fpu, sig, k, shape):
    if leg.startswith("rv32"):
        if shape == "w" and "f32" in sig:
            return False  # RV32 has no `i32.reinterpret_f32` (an op decline)
        homes = rv32_homes(sig)
        return all(isinstance(homes[j], tuple) for j in touched(sig, k, shape))
    if fpu is None:
        # soft-float ARM: an f32 signature declines on the direct selector
        # (GI-FPU-002) but the self-contained optimized path takes some of
        # them with the integer ABI, which IS the soft-float ABI — so either
        # outcome is legal (None: not pinned, not in the floor, RUN if
        # compiled). An f64 param is a core pair, declined where an f64 op
        # touches it.
        if "f32" in sig:
            return None
        if shape == "w" and "f64" in sig:
            return False
    return True


# ── reference ────────────────────────────────────────────────────────────────

def vectors(sig, name):
    rng = random.Random(f"vec:{name}")
    vecs = []
    for v in range(NVEC):
        args = []
        for t in sig:
            if t == "i32":
                args.append(rng.choice([0, 1, 3, 5, 7]) if v == 0 else rng.getrandbits(32))
            elif t == "i64":
                args.append(rng.getrandbits(64))
            elif t == "f32":
                args.append(struct.unpack("<I", struct.pack("<f", rng.uniform(-1e3, 1e3)))[0])
            else:
                args.append(struct.unpack("<Q", struct.pack("<d", rng.uniform(-1e9, 1e9)))[0])
        vecs.append(args)
    return vecs


def to_wasm(t, bits):
    if t == "i32":
        return bits - (1 << 32) if bits >> 31 else bits
    if t == "i64":
        return bits - (1 << 64) if bits >> 63 else bits
    if t == "f32":
        return struct.unpack("<f", struct.pack("<I", bits))[0]
    return struct.unpack("<d", struct.pack("<Q", bits))[0]


def reference(wat, funcs):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wat)
    ref = {}
    for name, sig, _, _ in funcs:
        for vi, args in enumerate(vectors(sig, name)):
            store = wasmtime.Store(eng)
            inst = wasmtime.Instance(store, mod, [])
            v = inst.exports(store)[name](store, *[to_wasm(t, a) for t, a in zip(sig, args)])
            ref[(name, vi)] = v & M32
    return ref


# ── compile + execute ────────────────────────────────────────────────────────

def compile_leg(src, flags, tmp, leg):
    out = os.path.join(tmp, f"{leg}.o")
    r = subprocess.run([SYNTH, "compile", str(src), *flags, "--all-exports",
                        "--allow-skipped-exports", "-o", out],
                       capture_output=True, text=True)
    text = r.stdout + r.stderr
    skipped = dict(re.findall(r"skipping function '([^']+)': (.*)", text))
    return r.returncode, out, skipped, text


R_ARM_THM_CALL, R_ARM_CALL, R_RISCV_CALL_PLT, R_RISCV_CALL = 10, 28, 18, 19


def patch(text, off, rtype, target):
    """Resolve one call relocation in place, as a linker would."""
    if rtype == R_ARM_THM_CALL:
        d = (target & ~1) - (off + 4)
        sb, i1, i2 = (d >> 24) & 1, (d >> 23) & 1, (d >> 22) & 1
        j1, j2 = (~i1 ^ sb) & 1, (~i2 ^ sb) & 1
        hw1 = 0xF000 | sb << 10 | (d >> 12) & 0x3FF
        hw2 = 0xD000 | j1 << 13 | j2 << 11 | (d >> 1) & 0x7FF
        struct.pack_into("<HH", text, off, hw1, hw2)
    elif rtype == R_ARM_CALL:
        (w,) = struct.unpack_from("<I", text, off)
        struct.pack_into("<I", text, off, (w & 0xFF00_0000)
                         | ((target - (off + 8)) >> 2) & 0xFF_FFFF)
    elif rtype in (R_RISCV_CALL, R_RISCV_CALL_PLT):
        d = target - off
        (auipc, jalr) = struct.unpack_from("<II", text, off)
        if auipc & 0x7F != 0x17 or jalr & 0x7F != 0x67:
            sys.exit(f"REFUSE: reloc site {off:#x} is not an auipc/jalr pair")
        struct.pack_into("<II", text, off, (auipc & 0xFFF) | (((d + 0x800) >> 12) & 0xFFFFF) << 12,
                         (jalr & 0x000F_FFFF) | (d & 0xFFF) << 20)
    else:
        sys.exit(f"REFUSE: unexpected relocation type {rtype} at {off:#x}")


def load_sections(path):
    """(function symbols, [(addr, bytes)]) with .text call relocations applied."""
    with open(path, "rb") as fh:
        ef = ELFFile(fh)
        symtab = next(s for s in ef.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        syms = {s.name: s["st_value"] for s in symtab.iter_symbols()
                if s.name and s["st_info"]["type"] == "STT_FUNC"}
        secs = []
        for idx, sec in enumerate(ef.iter_sections()):
            if not (sec["sh_flags"] & 2 and sec["sh_type"] == "SHT_PROGBITS"):
                continue
            data = bytearray(sec.data())
            for rs in ef.iter_sections():
                if rs["sh_type"] in ("SHT_REL", "SHT_RELA") and rs["sh_info"] == idx:
                    for r in rs.iter_relocations():
                        sym = symtab.get_symbol(r["r_info_sym"])
                        if sym["st_shndx"] != idx:
                            sys.exit(f"REFUSE: {path}: relocation against {sym.name!r}, "
                                     "which is not defined in the same section")
                        patch(data, r["r_offset"], r["r_info_type"], sym["st_value"])
            secs.append((sec["sh_addr"], bytes(data)))
    return syms, secs


def new_uc(arch, mode, secs):
    uc = Uc(arch, mode)
    pages = set()
    for a, d in secs:
        for p in range(a & ~0xFFF, a + max(len(d), 1), 0x1000):
            pages.add(p)
    for p in sorted(pages):
        uc.mem_map(p, 0x1000)
    for a, d in secs:
        uc.mem_write(a, d)
    for base, size in ((RET, 0x1000), (STACK, STACK_SIZE), (SCRATCH, 0x1000)):
        uc.mem_map(base, size)
    # Poison the frame area BELOW the entry SP, so a read of a slot nobody
    # stored returns a recognisable word rather than unicorn's zero fill.
    uc.mem_write(STACK, struct.pack("<I", 0xDEADBEEF) * ((SP0 - STACK) // 4))
    return uc


def aapcs(sig, args, vfp):
    """(core words by register 0..3, stack bytes, [(S-index, bits)], [(D-index, bits)])."""
    core, stack = [None] * 4, bytearray()
    ncrn, stage_c = 0, False
    s_taken, s_args, d_args = [False] * 16, [], []
    for t, a in zip(sig, args):
        if vfp and t == "f32":
            k = s_taken.index(False)
            s_taken[k] = True
            s_args.append((k, a))
            continue
        if vfp and t == "f64":
            k = next(k for k in range(8) if not s_taken[2 * k] and not s_taken[2 * k + 1])
            s_taken[2 * k] = s_taken[2 * k + 1] = True
            d_args.append((k, a))
            continue
        if t in WIDE:
            if ncrn % 2:
                ncrn += 1
            if ncrn <= 2 and not stage_c:
                core[ncrn], core[ncrn + 1] = a & M32, a >> 32
                ncrn += 2
            else:
                ncrn, stage_c = 4, True
                if len(stack) % 8:
                    stack += b"\0" * 4
                stack += struct.pack("<Q", a)
        elif ncrn <= 3 and not stage_c:
            core[ncrn] = a & M32
            ncrn += 1
        else:
            ncrn, stage_c = 4, True
            stack += struct.pack("<I", a & M32)
    return core, bytes(stack), s_args, d_args


def run_arm(uc, thumb, fpu, entry, sig, args, rng):
    pick = (lambda: rng.getrandbits(32)) if rng else (lambda: 0)
    if thumb:
        uc.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)
        uc.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)
        for i in range(32 if fpu == "dp" else 16):
            uc.reg_write(getattr(A, f"UC_ARM_REG_S{i}"), pick())
    core, stack, s_args, d_args = aapcs(sig, args, fpu is not None)
    for i in range(4):
        uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), core[i] if core[i] is not None else pick())
    for i in (4, 5, 6, 7, 8, 12):
        uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), pick())
    for i in (9, 10, 11):
        uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), SCRATCH)
    for k, bits in s_args:
        uc.reg_write(getattr(A, f"UC_ARM_REG_S{k}"), bits)
    for k, bits in d_args:
        uc.reg_write(getattr(A, f"UC_ARM_REG_D{k}"), bits)
    uc.mem_write(SP0, stack + bytes(64))
    uc.reg_write(A.UC_ARM_REG_SP, SP0)
    uc.reg_write(A.UC_ARM_REG_LR, RET | (1 if thumb else 0))
    try:
        uc.emu_start((entry & ~1) | (1 if thumb else 0), RET, count=20_000)
    except UcError as e:
        return f"fault:{e}"
    if uc.reg_read(A.UC_ARM_REG_PC) & ~1 != RET:
        return "did-not-return"
    return uc.reg_read(A.UC_ARM_REG_R0) & M32


def ilp32(sig, args):
    regs, stack, n = [None] * 8, bytearray(), 0
    for t, a in zip(sig, args):
        if t in WIDE:
            if n <= 6:
                regs[n], regs[n + 1] = a & M32, a >> 32
                n += 2
            elif n == 7:
                regs[7] = a & M32
                stack += struct.pack("<I", a >> 32)
                n = 8
            else:
                if len(stack) % 8:
                    stack += b"\0" * 4
                stack += struct.pack("<Q", a)
        elif n < 8:
            regs[n] = a & M32
            n += 1
        else:
            stack += struct.pack("<I", a & M32)
    return regs, bytes(stack)


def run_rv32(uc, entry, sig, args, rng):
    pick = (lambda: rng.getrandbits(32)) if rng else (lambda: 0)
    regs, stack = ilp32(sig, args)
    for i in range(8):
        uc.reg_write(getattr(RV, f"UC_RISCV_REG_A{i}"), regs[i] if regs[i] is not None else pick())
    for i in range(7):
        uc.reg_write(getattr(RV, f"UC_RISCV_REG_T{i}"), pick())
    uc.mem_write(SP0, stack + bytes(64))
    uc.reg_write(RV.UC_RISCV_REG_SP, SP0)
    uc.reg_write(RV.UC_RISCV_REG_S11, SCRATCH)
    uc.reg_write(RV.UC_RISCV_REG_RA, RET)
    try:
        uc.emu_start(entry, RET, count=20_000)
    except UcError as e:
        return f"fault:{e}"
    if uc.reg_read(RV.UC_RISCV_REG_PC) != RET:
        return "did-not-return"
    return uc.reg_read(RV.UC_RISCV_REG_A0) & M32


def expected_emulations(funcs):
    n = 0
    for leg, _, _, _, fpu in LEGS:
        n += sum(1 for _, sig, k, sh in funcs if expect_compiled(leg, fpu, sig, k, sh) is True)
    return n * NVEC * len(STATES)


def declared_floor():
    src = Path(__file__).read_text()
    m = re.search(r"^# ci-checks: emulations >= (\d+)$", src, re.M)
    if not m:
        sys.exit("REFUSE: no `# ci-checks: emulations >= N` header in this file")
    return int(m.group(1))


def main():
    funcs, wat = build_fixture()
    want, floor = expected_emulations(funcs), declared_floor()
    if want != floor:
        sys.exit(f"REFUSE: the declared floor is `emulations >= {floor}` but the leg "
                 f"rules derive {want} — fix the header, not the rules")
    ref = reference(wat, funcs)
    failures, emulations, per_leg = [], 0, {}
    with tempfile.TemporaryDirectory(prefix="pai1714_") as tmp:
        src = Path(tmp) / "param_after_wide_1714.wat"
        src.write_text(wat)
        for leg, backend, flags, mode, fpu in LEGS:
            rc, path, skipped, text = compile_leg(src, flags, tmp, leg)
            if rc != 0:
                failures.append(f"{leg}: compile rc={rc}: {text.strip().splitlines()[-1:]}")
                per_leg[leg] = "compile failed"
                continue
            rule = {n: expect_compiled(leg, fpu, sig, k, sh) for n, sig, k, sh in funcs}
            expect_skip = {n for n, r in rule.items() if r is False}
            either = {n for n, r in rule.items() if r is None}
            expect_run = {n for n, r in rule.items() if r is not False} - set(skipped)
            if set(skipped) - either != expect_skip:
                extra = sorted(set(skipped) - either - expect_skip)
                missing = sorted(expect_skip - set(skipped))
                if extra:
                    failures.append(f"{leg}: declined but should compile: {extra}")
                if missing:
                    failures.append(f"{leg}: COMPILED but must be declined: {missing}")
            syms, secs = load_sections(path)
            if backend == "riscv":
                uc = new_uc(UC_ARCH_RISCV, UC_MODE_RISCV32, secs)
            else:
                uc = new_uc(UC_ARCH_ARM, UC_MODE_THUMB if mode == "thumb" else UC_MODE_ARM, secs)
            bad, bad_names = 0, set()
            for name, sig, _, _ in funcs:
                if name not in expect_run or name not in syms:
                    continue
                for state in STATES:
                    rng = random.Random(f"{leg}:{name}:{state}") if state == "garbage" else None
                    for vi, args in enumerate(vectors(sig, name)):
                        if backend == "riscv":
                            g = run_rv32(uc, syms[name], sig, args, rng)
                        else:
                            g = run_arm(uc, mode == "thumb", fpu, syms[name], sig, args, rng)
                        emulations += 1
                        w = ref[(name, vi)]
                        if g != w:
                            bad += 1
                            bad_names.add(name)
                            shown = f"{g:#x}" if isinstance(g, int) else g
                            failures.append(f"{leg} {state} {name}{tuple(hex(a) for a in args)}: "
                                            f"synth {shown}, wasmtime {w:#x}")
            per_leg[leg] = f"{bad} disagreeing call(s), {len(expect_run)} export(s) run, " \
                           f"{len(skipped)} declined" + \
                           (f"\n      wrong: {' '.join(sorted(bad_names))}" if bad_names else "")
    for leg, s in per_leg.items():
        print(f"  {leg:11s} {s}")
    failures.sort(key=lambda f: "declined" not in f and "COMPILED" not in f)
    for f in failures[:40]:
        print("FAIL:", f)
    if len(failures) > 40:
        print(f"... and {len(failures) - 40} more")
    print(f"param-after-wide: {len(funcs)} exports, {emulations} emulation(s), "
          f"{len(failures)} failure(s), floor {floor}")
    ok = not failures and emulations >= floor
    print("RESULT: PASS" if ok else "RESULT: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
