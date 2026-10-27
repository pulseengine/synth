#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 210
"""#1593 (RQ-89-WIDESTAGE) — EXECUTION-validate float CALL-ARGUMENT STAGING
on the `vfp-wide-file` rung (cortex-m7 and cortex-m7dp, `--relocatable`).

The defect: the wide-file rung (#1267/#1439) hands out real S16..S31, and an
f32 call argument computed while S0..S15 are full lands in one of them. The
float-argument move (`emit_vfp_arg_moves`) parks every moving source in the
VFP call-spill area at `base + 4*(its S-index)` and reloads it into its
AAPCS-VFP argument register. That area is 16 words; the source index went to
31. So a source in S(16+k) was

  * STORED FROM S(k) — the slot->register map used for the store wrapped
    `% 16`, the second site of the #1439 wrap PR #1585 fixed in the pool
    (`vstr s1,[sp,#0x44]` observed for S17 on #1318's module), and
  * stored to a slot PAST THE AREA, i.e. into whatever the frame keeps
    there — on #1318's `step`, the frame home of a live integer local.

Before #1585 every such function was refused loudly; v0.88.0 is unaffected.

The fix (RQ-89-WIDESTAGE) stores from the unwrapped S-file table and sizes the
area 32 words when the wide-file rung is on. Both halves are needed and this
oracle pins each separately — measured on half-fixed binaries: register-only
(16-word area) leaves `stagel` red, 66 of 210; slot-only (store still wrapped)
leaves all three red, 130 of 210. The unfixed base is red 148 of 210.

Fixture (generated in-process — nothing here is derived from the external
#1318 module): N_LOCALS f32 locals all live at once, so the function lands on
`vfp-wide-file` (gate 1 asserts it from SYNTH_RECOVERY_STATS); a right-leaning
sum keeps PEND of them pending on the operand stack while a call to the local
`$g` evaluates six f32 arguments, so the argument temps are granted S16..S31.
`$g` weights its arguments 1,2,4,...,32, so a swapped or wrong-register
argument changes the result. The rest of the locals are summed after the call
(values live across it). `stagei` adds an i32 param live across the call;
`stagel` adds N_ILOCALS i32 LOCALS, declared first so they take the lowest
frame offsets, read only AFTER the call — on the unfixed binary a staging
store past the 16-word area lands on one of their homes (the integer-frame
overlap #1318's `step` hit on its shadow-stack pointer).

THE SIZES ARE A WINDOW, not decoration: fewer f32 locals and the function is
rescued by an earlier rung (gate 1 reds); more, and the 32-word area pushes a
frame-home slot past the 1020-byte VSTR/VLDR reach, so the fixed compiler
REFUSES it loudly (measured: 58 and 60 locals) — the narrowing this fix makes,
from a silent miscompile on main to the loud decline v0.88 gave.

Gates:
  1. compile — both targets, every export `nm -> T`, and every `stage*`
     export produced BY the vfp-wide-file rung;
  2. STAGING SHAPE — in each `stage*` function an argument temp is computed
     INTO S16..S31 before the `bl` (a `vmul.f32 s16..s31`: the local.set
     prologue runs with an empty operand stack, so its multiplies land in
     S0..S15 and a hit is an argument temp), so
     the argument move has a wide-file source; else the fixture stopped
     reaching the path and the executions below would be vacuous. This is a
     property of the ALLOCATION, deliberately not of the staging store, so it
     holds on the defective binary too (whose store names S0..S15);
  3. EXECUTE bit-identically to wasmtime under unicorn, with GARBAGE in every
     caller-saved register (R0..R3, R12, S1..S15) and in the whole stack, and
     with callee-saved R4..R11 / S16..S31 / SP / the caller's stack above SP
     checked unchanged after return.

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld/objdump):
  SYNTH=/path/to/synth python scripts/repro/vfp_wide_stage_1593_differential.py
"""

import os
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn import arm_const as A

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
TARGETS = ["cortex-m7", "cortex-m7dp"]
N_LOCALS = 56
# Pending depth: how many locals sit on the operand stack while the call's
# arguments are evaluated. 24 puts the six argument temps in S16..S31.
PEND = 24
STAGE_EXPORTS = ["stage", "stagei", "stagel"]
# i32 locals in `stagel`: enough that the staging slots past the 16-word area
# reach one of their homes on the unfixed binary.
N_ILOCALS = 12
N_F32_STAGEL = 54

G = """  (func $g (param f32 f32 f32 f32 f32 f32) (result f32)
    (f32.add (local.get 0) (f32.add (f32.mul (local.get 1) (f32.const 2))
     (f32.add (f32.mul (local.get 2) (f32.const 4)) (f32.add (f32.mul (local.get 3) (f32.const 8))
     (f32.add (f32.mul (local.get 4) (f32.const 16)) (f32.mul (local.get 5) (f32.const 32))))))))"""


def stage_func(name, with_i32, n_ilocals=0, n_f32=None):
    """`with_i32`: an i32 param live across the call. `n_ilocals`: that many
    i32 LOCALS (declared first, so they take the lowest frame offsets — the
    ones a staging store past the 16-word area lands on), each derived from
    the param and summed after the call."""
    n_f32 = n_f32 or N_LOCALS
    params = "(param $a f32)" + (" (param $p i32)" if with_i32 else "")
    first_i = 2 if with_i32 else 1
    off = first_i + n_ilocals

    def lg(k):  # f32 local k in 1..n_f32
        return f"(local.get {k + off - 1})"

    out = [f'  (func ${name} (export "{name}") {params} (result f32)']
    if n_ilocals:
        out.append("    (local " + " ".join(["i32"] * n_ilocals) + ")")
    out.append("    (local " + " ".join(["f32"] * n_f32) + ")")
    for i in range(n_ilocals):
        out.append(f"    (local.set {first_i + i} (i32.add (i32.mul "
                   f"(local.get 1) (i32.const {2 * i + 3})) (i32.const {i + 1})))")
    for k in range(1, n_f32 + 1):
        out.append(f"    (local.set {k + off - 1} "
                   f"(f32.mul (local.get 0) (f32.const {k}.5)))")
    args = " ".join(f"(f32.mul {lg(PEND + j)} (f32.const {j}.25))"
                    for j in range(1, 7))
    inner = lg(n_f32)
    for k in range(n_f32 - 1, PEND, -1):
        inner = f"(f32.add {lg(k)} {inner})"
    if with_i32:
        # Right of the call, so every i32 is READ AFTER it returns: a staging
        # store that landed on one of their frame slots is observed.
        isum = "(local.get 1)"
        for i in range(n_ilocals):
            isum = f"(i32.xor {isum} (local.get {first_i + i}))"
        inner = f"(f32.add (f32.convert_i32_s {isum}) {inner})"
    inner = f"(f32.add (call $g {args}) {inner})"
    for k in range(PEND, 0, -1):
        inner = f"(f32.add {lg(k)} {inner})"
    out.append("    " + inner + ")")
    return "\n".join(out)


def wat_text():
    return "\n".join(["(module", G, stage_func("stage", False),
                      stage_func("stagei", True),
                      stage_func("stagel", True, N_ILOCALS, N_F32_STAGEL), ")"]) + "\n"


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_obj(tmp, wat, target):
    obj = str(Path(tmp) / f"ws1593_{target}.o")
    r = subprocess.run(
        [SYNTH, "compile", str(wat), "-o", obj, "-t", target, "--relocatable"],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        env={**os.environ, "SYNTH_RECOVERY_STATS": "1"},
    )
    if r.returncode != 0:
        fail(f"[{target}] compile failed:\n{r.stdout}")
    if "skipping function" in r.stdout:
        fail(f"[{target}] a function was skipped:\n{r.stdout}")
    return obj, r.stdout


def final_rungs(log):
    out, cur = {}, None
    for line in log.splitlines():
        m = re.search(r"Compiling function '([^']+)'", line)
        if m:
            cur = m.group(1)
        elif "[recovery-stats] rung=" in line and cur is not None:
            out[cur] = line.strip()
    return out


def text_symbols(obj):
    with open(obj, "rb") as fh:
        ef = ELFFile(fh)
        symtab = next((s for s in ef.iter_sections()
                       if s["sh_type"] == "SHT_SYMTAB"), None)
        if symtab is None:
            fail("relocatable object has no SHT_SYMTAB section")
        names = set()
        for sym in symtab.iter_symbols():
            if not sym.name or sym["st_info"]["bind"] != "STB_GLOBAL":
                continue
            shndx = sym["st_shndx"]
            if shndx in ("SHN_UNDEF", "SHN_ABS", "SHN_COMMON"):
                continue
            if ef.get_section(shndx)["sh_flags"] & 0x4:  # SHF_EXECINSTR
                names.add(sym.name)
    return names


def link(tmp, obj, target):
    ld = shutil.which("arm-none-eabi-ld")
    if ld is None:
        fail("arm-none-eabi-ld not found")
    out = str(Path(tmp) / f"ws1593_{target}.elf")
    r = subprocess.run([ld, "-e", "stage", "-Ttext=0x0", obj, "-o", out],
                       capture_output=True, text=True)
    if r.returncode != 0 or r.stderr.strip():
        fail(f"link failed / diagnostics:\n{r.stderr}")
    return out


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return text.data(), text["sh_addr"], syms


HIGH_DEF = re.compile(r"\bvmul\.f32\s+s(1[6-9]|2[0-9]|3[01]),")


def staging_shape(obj, syms, name):
    """Count multiplies INTO S16..S31 before the first `bl` (gate 2)."""
    objdump = shutil.which("arm-none-eabi-objdump")
    if objdump is None:
        fail("arm-none-eabi-objdump not found")
    # Thumb symbols carry bit 0; disassembling from an odd address misaligns.
    lo = syms[name] & ~1
    # Function symbols only: `$t`/`$d` mapping symbols sit INSIDE a function.
    hi = min([v & ~1 for k, v in syms.items()
              if (v & ~1) > lo and not k.startswith("$")] or [lo + 0x10000])
    # The RELOCATABLE object, not the linked image: the image carries no `$t`
    # mapping symbols, so objdump prints every halfword pair as `.word` and the
    # gate would match nothing. One .text at 0 => the same offsets.
    dis = subprocess.run([objdump, "-d", f"--start-address={lo:#x}",
                          f"--stop-address={hi:#x}", obj],
                         capture_output=True, text=True, check=True).stdout
    n = 0
    for line in dis.splitlines():
        if re.search(r"\bbl\b", line):
            return n
        if HIGH_DEF.search(line):
            n += 1
    return n


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def is_nan32(b):
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


STACK_BASE, STACK_SIZE, SP0 = 0x30000, 0x10000, 0x38000
RET = 0x3F000  # return trap address, inside the mapped (garbage) stack page
CALLER_SAVED = [A.UC_ARM_REG_R0, A.UC_ARM_REG_R1, A.UC_ARM_REG_R2,
                A.UC_ARM_REG_R3, A.UC_ARM_REG_R12]
CALLEE_SAVED = [getattr(A, f"UC_ARM_REG_R{i}") for i in range(4, 12)]
S_REGS = [getattr(A, f"UC_ARM_REG_S{i}") for i in range(32)]


def run(text, base, addr, a_bits, p, rng):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    try:
        uc.ctl_set_cpu_model(A.UC_CPU_ARM_MAX)
    except AttributeError:
        pass
    map_base = base & ~0xFFF
    size = ((len(text) + (base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(base, text)
    uc.mem_map(STACK_BASE, STACK_SIZE)
    stack = bytes(rng.getrandbits(8) for _ in range(STACK_SIZE))
    uc.mem_write(STACK_BASE, stack)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    for r in CALLER_SAVED:
        uc.reg_write(r, rng.getrandbits(32))
    callee = {r: rng.getrandbits(32) for r in CALLEE_SAVED}
    for r, v in callee.items():
        uc.reg_write(r, v)
    s_hi = {}
    for i, r in enumerate(S_REGS):
        v = rng.getrandbits(32)
        uc.reg_write(r, v)
        if i >= 16:
            s_hi[r] = v
    uc.reg_write(A.UC_ARM_REG_S0, a_bits)
    if p is not None:
        uc.reg_write(A.UC_ARM_REG_R0, p & 0xFFFFFFFF)
    uc.reg_write(A.UC_ARM_REG_SP, SP0)
    uc.reg_write(A.UC_ARM_REG_LR, RET | 1)
    uc.emu_start(addr | 1, RET, count=20000)
    if uc.reg_read(A.UC_ARM_REG_PC) & ~1 != RET:
        return None, "did not return"
    if uc.reg_read(A.UC_ARM_REG_SP) != SP0:
        return None, "SP not restored"
    for r, v in callee.items():
        if uc.reg_read(r) != v:
            return None, f"callee-saved core reg {r} clobbered"
    for r, v in s_hi.items():
        if uc.reg_read(r) & 0xFFFFFFFF != v:
            return None, f"callee-saved S-reg {r} clobbered"
    above = bytes(uc.mem_read(SP0, STACK_BASE + STACK_SIZE - SP0))
    if above != stack[SP0 - STACK_BASE:]:
        return None, "caller's stack above SP written"
    return uc.reg_read(A.UC_ARM_REG_S0) & 0xFFFFFFFF, None


VALS = [0.0, -0.0, 1.0, -1.0, 0.5, -0.25, 1.5, 0.001, -3.14159265, 1e-30,
        -1e30, 7.0, float("inf"), float("-inf"), float("nan")]
PS = [0, -7, 123456]


def main():
    tmp = tempfile.mkdtemp(prefix="ws1593_")
    wat = Path(tmp) / "ws1593.wat"
    wat.write_text(wat_text())

    eng = wasmtime.Engine()
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, wasmtime.Module(eng, wat.read_text()), [])
    exp = inst.exports(store)

    checked = mismatches = 0
    first = None
    tally = {}
    for target in TARGETS:
        obj, log = compile_obj(tmp, wat, target)
        rungs = final_rungs(log)
        for name in STAGE_EXPORTS:
            got = rungs.get(name)
            if got != "[recovery-stats] rung=vfp-wide-file result=ok":
                fail(f"[{target}] {name}: not produced by vfp-wide-file: {got}")
        missing = [e for e in STAGE_EXPORTS if e not in text_symbols(obj)]
        if missing:
            fail(f"[{target}] exports missing from nm -> T: {missing}")
        print(f"PASS: [{target}] {STAGE_EXPORTS} compiled through vfp-wide-file")

        elf = link(tmp, obj, target)
        text, base, syms = load(elf)
        for name in STAGE_EXPORTS:
            n = staging_shape(obj, syms, name)
            if n == 0:
                fail(f"[{target}] {name}: no argument temp in S16..S31 before "
                     "the call — the fixture no longer stages wide-file "
                     "arguments, so the executions below would be vacuous")
            print(f"PASS: [{target}] {name}: {n} argument temp(s) computed "
                  "into S16..S31 before the call")

        rng = random.Random(1593)
        for name in STAGE_EXPORTS:
            for a in VALS:
                for p in (PS if name != "stage" else [None]):
                    args = (a,) if p is None else (a, p)
                    want = f32_bits(exp[name](store, *args))
                    got, err = run(text, base, syms[name], f32_bits(a), p, rng)
                    checked += 1
                    ok = err is None and (
                        got == want or (is_nan32(got) and is_nan32(want)))
                    if not ok:
                        mismatches += 1
                        key = (target, name, "wrong value" if err is None else err)
                        tally[key] = tally.get(key, 0) + 1
                        if first is None:
                            first = (f"[{target}] {name}{args}: "
                                     + (err or f"got {got:#010x}, want {want:#010x}"))
    if mismatches:
        for (tg, nm, why), cnt in sorted(tally.items()):
            print(f"  [{tg}] {nm}: {cnt} x {why}")
        fail(f"{mismatches} of {checked} emulations disagree with wasmtime; "
             f"first: {first}")
    print(f"PASS: {checked} emulations bit-identical to wasmtime (garbage "
          "caller-saved regs + stack; callee-saved regs, SP and the caller's "
          "frame intact)")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
