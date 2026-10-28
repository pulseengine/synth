#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 240
"""#1318 (RQ-89-FALCONSTEP) — the vfp-wide-file call staging that VCR-RA-003
REFUSED although the emitted code was right, EXECUTION-validated.

The refusal: on the `vfp-wide-file` rung (#1267/#1439) a call's float
argument move (#1593) preserves every live caller-saved S-register into the
VFP call-spill area at `base + 4*(S-index)`, then parks each MOVING argument
source at the same `base + 4*(its S-index)` — so an argument that is a live
low S-register (a register-homed local passed directly) is stored to its
slot TWICE with the same untouched value. The #881 slot check treats that as
benign (same source word, same def-version) — unless an S16..S31 staging
store sits between the two, because `liveness::vfp_reg_words` mapped only
S0..S15: the S16+ store's `vfp_word_effect` was `None`, the check widened it
to "every word redefined", and the identical re-store read as a SECOND
value: `VfpSpillSlotAliased`, "refusing to emit a miscompiled object". That
is what refused the external reporter's `step` (slot 20) after #1594's entry
zero-init moved its allocation; the stream was byte-identical with the
validator fixed, and ran bit-identical to wasmtime over the reporter's own
1000-call workload. The other direction of the same gap was a real hole: an
S16+ store never entered the slot tracking, so an S16+ store OVER a live slot
was invisible (pinned red-first by
`ra003_vfp_slot_high_bank_store_alias_caught_1318` in liveness.rs).

Fixture (generated in-process — nothing here is derived from the external
#1318 module): the #1593 shape (N_LOCALS f32 locals live at once, PEND of
them pending on the operand stack while six f32 arguments are evaluated, so
argument temps land in S16..S31), with one argument a DIRECT `local.get` of a
register-homed local that is also read after the call. `rs1`/`rs3`/`rs5`
vary which low home (S1/S3/S5 class); `rsz` passes a local written on only
one path (read-before-write, so #1594 homes and zeroes it at entry — the
interaction the reporter's module hit).

Gates:
  1. compile — both targets, every export `nm -> T`, each produced BY the
     `vfp-wide-file` rung (SYNTH_RECOVERY_STATS);
  2. SHAPE — in each function, before its first `bl`, some low `vstr sN,
     [sp,#X]` (N < 16) is repeated with a `vstr s16..s31` between the two:
     the exact sequence the unfixed validator refused. A property of the
     emitted stream, so it holds on the refusing binary's selection too;
     without it the executions below would not exercise the path;
  3. EXECUTE bit-identically to wasmtime under unicorn, twice per vector:
     GARBAGE caller-saved registers (R0..R3, R12, S1..S15) + GARBAGE stack,
     and a ZEROED machine — callee-saved R4..R11 / S16..S31 / SP / the
     caller's stack above SP checked unchanged after return.

Red-first: on origin/main 9f123a65 every export is refused (VCR-RA-003
VfpSpillSlotAliased), so gate 1 fails. Fixed: all gates pass.

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld/objdump):
  SYNTH=/path/to/synth python scripts/repro/vfp_high_bank_restore_1318_differential.py
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
# The #1593 window: fewer locals and an earlier rung rescues the function;
# more and a frame home passes the 1020-byte VSTR/VLDR reach.
N_LOCALS = 56
PEND = 24
# export name -> the low-homed local passed directly as argument 3 (None =
# the read-before-write local `rsz` declares after the N_LOCALS block).
EXPORTS = {"rs1": 1, "rs3": 3, "rs5": 5, "rsz": None}

G = """  (func $g (param f32 f32 f32 f32 f32 f32) (result f32)
    (f32.add (local.get 0) (f32.add (f32.mul (local.get 1) (f32.const 2))
     (f32.add (f32.mul (local.get 2) (f32.const 4)) (f32.add (f32.mul (local.get 3) (f32.const 8))
     (f32.add (f32.mul (local.get 4) (f32.const 16)) (f32.mul (local.get 5) (f32.const 32))))))))"""


def func(name, home):
    def lg(k):
        return f"(local.get {k})"

    z = N_LOCALS + 1  # the read-before-write local in `rsz`
    decl = ["f32"] * N_LOCALS + (["f32"] if home is None else [])
    out = [f'  (func ${name} (export "{name}") (param $a f32) (result f32)',
           "    (local " + " ".join(decl) + ")"]
    if home is None:
        # Written on one path only: wasm reads 0.0 at the join when a <= 0.
        out.append(f"    (if (f32.gt (local.get 0) (f32.const 0)) (then "
                   f"(local.set {z} (f32.mul (local.get 0) (f32.const 3)))))")
    for k in range(1, N_LOCALS + 1):
        out.append(f"    (local.set {k} (f32.mul (local.get 0) (f32.const {k}.5)))")
    direct = lg(z if home is None else home)
    # Argument 3 (S2) for the numbered homes; argument 4 (S3) for `rsz`,
    # whose entry-zeroed home is granted S2 itself — a source already in its
    # argument register does not move, so it would never be re-stored.
    pos = 4 if home is None else 3
    args = " ".join(direct if j == pos else f"(f32.mul {lg(PEND + j)} (f32.const {j}.25))"
                    for j in range(1, 7))
    inner = lg(N_LOCALS)
    for k in range(N_LOCALS - 1, PEND, -1):
        inner = f"(f32.add {lg(k)} {inner})"
    if home is None:
        inner = f"(f32.add {lg(z)} {inner})"  # read after the call too
    inner = f"(f32.add (call $g {args}) {inner})"
    for k in range(PEND, 0, -1):
        inner = f"(f32.add {lg(k)} {inner})"
    out.append("    " + inner + ")")
    return "\n".join(out)


def wat_text():
    return "\n".join(["(module", G] + [func(n, h) for n, h in EXPORTS.items()]
                     + [")"]) + "\n"


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_obj(tmp, wat, target):
    obj = str(Path(tmp) / f"hb1318_{target}.o")
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
    out = str(Path(tmp) / f"hb1318_{target}.elf")
    r = subprocess.run([ld, "-e", "rs1", "-Ttext=0x0", obj, "-o", out],
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


VSTR = re.compile(r"\bvstr\s+s(\d+),\s*\[sp,\s*#(\d+)\]")


def restore_shape(obj, syms, name):
    """Gate 2: (low reg, slot) pairs stored twice before the first `bl` with
    an S16..S31 store between the two."""
    objdump = shutil.which("arm-none-eabi-objdump")
    if objdump is None:
        fail("arm-none-eabi-objdump not found")
    lo = syms[name] & ~1
    hi = min([v & ~1 for k, v in syms.items()
              if (v & ~1) > lo and not k.startswith("$")] or [lo + 0x10000])
    # The RELOCATABLE object (it carries the `$t` mapping symbols).
    dis = subprocess.run([objdump, "-d", f"--start-address={lo:#x}",
                          f"--stop-address={hi:#x}", obj],
                         capture_output=True, text=True, check=True).stdout
    seen = {}  # (reg, slot) -> high-bank stores seen since its first store
    hits = set()
    for line in dis.splitlines():
        if re.search(r"\bbl\b", line):
            break
        m = VSTR.search(line)
        if not m:
            continue
        reg, slot = int(m.group(1)), int(m.group(2))
        if reg >= 16:
            for key in seen:
                seen[key] = True
        elif (reg, slot) in seen and seen[(reg, slot)]:
            hits.add((reg, slot))
        else:
            seen[(reg, slot)] = False
    return hits


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def is_nan32(b):
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


STACK_BASE, STACK_SIZE, SP0 = 0x30000, 0x10000, 0x38000
RET = 0x3F000  # return trap address, inside the mapped stack page
CALLER_SAVED = [A.UC_ARM_REG_R0, A.UC_ARM_REG_R1, A.UC_ARM_REG_R2,
                A.UC_ARM_REG_R3, A.UC_ARM_REG_R12]
CALLEE_SAVED = [getattr(A, f"UC_ARM_REG_R{i}") for i in range(4, 12)]
S_REGS = [getattr(A, f"UC_ARM_REG_S{i}") for i in range(32)]


def run(text, base, addr, a_bits, rng, garbage):
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
    stack = (bytes(rng.getrandbits(8) for _ in range(STACK_SIZE)) if garbage
             else bytes(STACK_SIZE))
    uc.mem_write(STACK_BASE, stack)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    pick = (lambda: rng.getrandbits(32)) if garbage else (lambda: 0)
    for r in CALLER_SAVED:
        uc.reg_write(r, pick())
    callee = {r: pick() for r in CALLEE_SAVED}
    for r, v in callee.items():
        uc.reg_write(r, v)
    s_hi = {}
    for i, r in enumerate(S_REGS):
        v = pick()
        uc.reg_write(r, v)
        if i >= 16:
            s_hi[r] = v
    uc.reg_write(A.UC_ARM_REG_S0, a_bits)
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


def main():
    tmp = tempfile.mkdtemp(prefix="hb1318_")
    wat = Path(tmp) / "hb1318.wat"
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
        for name in EXPORTS:
            got = rungs.get(name)
            if got != "[recovery-stats] rung=vfp-wide-file result=ok":
                fail(f"[{target}] {name}: not produced by vfp-wide-file: {got}")
        missing = [e for e in EXPORTS if e not in text_symbols(obj)]
        if missing:
            fail(f"[{target}] exports missing from nm -> T: {missing}")
        print(f"PASS: [{target}] {list(EXPORTS)} compiled through vfp-wide-file")

        elf = link(tmp, obj, target)
        text, base, syms = load(elf)
        for name in EXPORTS:
            hits = restore_shape(obj, syms, name)
            if not hits:
                fail(f"[{target}] {name}: no low S-register re-stored to its "
                     "slot across an S16..S31 store before the call — the "
                     "fixture no longer reaches the refused shape, so the "
                     "executions below would be vacuous")
            print(f"PASS: [{target}] {name}: re-store across a high-bank "
                  f"store at {sorted(hits)}")

        rng = random.Random(1318)
        for name in EXPORTS:
            for a in VALS:
                want = f32_bits(exp[name](store, a))
                for garbage in (True, False):
                    got, err = run(text, base, syms[name], f32_bits(a), rng, garbage)
                    checked += 1
                    ok = err is None and (
                        got == want or (is_nan32(got) and is_nan32(want)))
                    if not ok:
                        mismatches += 1
                        state = "garbage" if garbage else "zeroed"
                        key = (target, name, state,
                               "wrong value" if err is None else err)
                        tally[key] = tally.get(key, 0) + 1
                        if first is None:
                            first = (f"[{target}] {name}({a}) {state}: "
                                     + (err or f"got {got:#010x}, want {want:#010x}"))
    if mismatches:
        for (tg, nm, st, why), cnt in sorted(tally.items()):
            print(f"  [{tg}] {nm} {st}: {cnt} x {why}")
        fail(f"{mismatches} of {checked} emulations disagree with wasmtime; "
             f"first: {first}")
    print(f"PASS: {checked} emulations bit-identical to wasmtime (garbage and "
          "zeroed machine; callee-saved regs, SP and the caller's frame intact)")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
