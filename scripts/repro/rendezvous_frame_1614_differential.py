#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 3608
"""#1614 (RQ-89-BRF32) — the f32 branch RENDEZVOUS slot must live IN the frame.

THE DEFECT. RQ-76-FALCON (#1318) carries an f32 over br/br_if/br_table to a
block join through a frame slot: every edge `vstr`s the value there and the
join `vldr`s it. The slot comes from the shared spill pool
(`alloc_vfp_local_frame_slot` -> `SpillState::alloc`). `compute_local_layout`
reserves that pool in the frame ONLY for an i64-touching function or on a
retry rung; otherwise the pool's base is just the end of the frame fields and
nothing is reserved there. So the slot landed on

  * the prologue's saved R4 when the function had no other frame use — no
    `sub sp` at all, `vstr s0,[sp]`, and the epilogue's `pop` handed the
    caller back the float's BITS in R4 (the issue's reduction);
  * a #204 param-backing slot when the function also makes a call;
  * the 8-byte rounding padding with an odd number of i32 locals — harmless
    by luck, which is why it is a class and not one shape.

With no call in the function the RETURN VALUE is right, so wasmtime agrees
and a value-only oracle (including #1318's own carried_float_branch oracle)
passes.
The violated contract is AAPCS: R4..R11 / S16..S31 / SP are callee-saved.

THE FIX. The rendezvous refuses to draw a slot from an UNRESERVED pool and
raises the ladder-recoverable spill-area Err, exactly as the #326 arg-move
resolver and the call-result parker already do; the backend's first retry rung
re-runs the function with the pool reserved. Only functions that actually
reach the rendezvous without a reserved pool move.

THIS ORACLE executes every row of the class (scripts/repro/rendezvous_frame_
1614.wat: br / br_if / br_table edges, a unary consumer, a br_if out of a loop, two slots, 0..3 i32 locals, an f32 local, a call before
and after the join, plus two CONTROLS) on cortex-m4f AND cortex-m7dp, both
self-contained and `--relocatable` (linked with arm-none-eabi-ld), under
unicorn with:

  * GARBAGE in every caller-saved register (R0..R3 beyond the args, R12,
    S0..S15 beyond the args) and in the whole stack;
  * RANDOM CANARIES in R4..R11 and S16..S31, checked unchanged after return,
    with SP restored and the caller's stack above SP unwritten;
  * the result BIT-EXACT against wasmtime (-0.0 and inf in the argument set).

RED on main 8e1097f6 (and d048b523): 1784 of 3608 emulations wrong, 10 of 16
rows — 8 by a clobbered R4, and `call_brif`/`call_after` by a WRONG VALUE (the
slot was a #204 param-backing slot). `loc1`/`loc3`/`locf`/`loop_brif` pass on
the base binary only because their slot fell in the frame padding. GREEN after
the fix: 3608 of 3608.

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld):
  SYNTH=/path/to/synth python3 scripts/repro/rendezvous_frame_1614_differential.py
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
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as A

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

HERE = Path(__file__).resolve().parent
WAT = HERE / "rendezvous_frame_1614.wat"
SYNTH = os.environ.get("SYNTH_BIN") or os.environ.get("SYNTH", "./target/debug/synth")
TARGETS = ("cortex-m4f", "cortex-m7dp")
MODES = ("self-contained", "relocatable")

# (export, params) — params drive the argument grid. Every export of the WAT
# (the helper `$h` is internal). `brif_i32` returns in R0, the rest in S0.
ROWS = (
    ("br_bare", ()),
    ("brif_drop", ("i32",)),
    ("br_p", ("f32",)),
    ("brif_p", ("f32", "i32")),
    ("brtable_p", ("f32", "i32")),
    ("unary_br", ("f32",)),
    ("loop_brif", ("f32", "i32")),
    ("nested2", ("f32", "i32")),
    ("loc1", ("f32", "i32")),
    ("loc2", ("f32", "i32")),
    ("loc3", ("f32", "i32")),
    ("locf", ("f32", "i32")),
    ("call_brif", ("f32", "i32")),
    ("call_after", ("f32", "i32")),
    ("i64op_brif", ("f32", "i32")),
    ("brif_i32", ("i32", "i32")),
)
# The rows that must REACH the rendezvous (a `vstr` to an SP-relative slot
# that the join `vldr`s). Gate 2 asserts each still does, so a fixture that
# drifted off the path cannot pass vacuously.
RENDEZVOUS_ROWS = {r for r, _ in ROWS} - {"brif_i32"}

# NaN is deliberately absent: an arithmetic result's NaN payload is not
# normative, so a bit-exact compare on it would pin non-spec behaviour.
F32_ARGS = (0.0, -0.0, 1.5, -3.75, float("inf"), 1e-30)
I32_ARGS = (0, 1, 2, 5, 0xFFFFFFFF, 0x80000000)
# Two independent machine states per argument tuple (different garbage and
# canaries), so a value that is right only for one register image is caught.
STATES = 2


def grid(params):
    out = [()]
    for p in params:
        vals = F32_ARGS if p == "f32" else I32_ARGS
        out = [t + (v,) for t in out for v in vals]
    return out


def expected_emulations():
    """DERIVE the floor from the row table (RQ-75-FLOORBIND, #1331): the header
    literal is read statically by oracle_wiring_check.py, so the binding runs
    the other way and the module REFUSES to run when the two disagree."""
    return sum(len(grid(p)) for _, p in ROWS) * STATES * len(TARGETS) * len(MODES)


def declared_floor():
    m = re.search(r"^# ci-checks: emulations >= (\d+)$", Path(__file__).read_text(), re.M)
    if not m:
        sys.exit("REFUSE: no `# ci-checks: emulations >= N` header in this file")
    return int(m.group(1))


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def compile_elf(tmp, target, mode):
    out = str(Path(tmp) / f"rf1614_{target}_{mode}.{'o' if mode == 'relocatable' else 'elf'}")
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-t", target, "--all-exports"]
    if mode == "relocatable":
        cmd.append("--relocatable")
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if r.returncode != 0:
        fail(f"[{target}/{mode}] compile failed:\n{r.stdout}")
    if "skipping function" in r.stdout.lower():
        fail(f"[{target}/{mode}] a function was skipped (newly refused):\n{r.stdout}")
    if mode == "relocatable":
        ld = shutil.which("arm-none-eabi-ld")
        if ld is None:
            fail("arm-none-eabi-ld not found")
        linked = out + ".elf"
        lr = subprocess.run([ld, "-e", "br_bare", "-Ttext=0x0", out, "-o", linked],
                            capture_output=True, text=True)
        if lr.returncode != 0 or lr.stderr.strip():
            fail(f"[{target}] link failed / diagnostics:\n{lr.stderr}")
        return out, linked
    return out, out


def load(elf):
    with open(elf, "rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text")
        syms = {}
        for s in f.iter_sections():
            if s.header.sh_type == "SHT_SYMTAB":  # #489: symtab, not disasm text
                for sym in s.iter_symbols():
                    if sym.name and sym["st_info"]["type"] == "STT_FUNC":
                        syms[sym.name] = sym["st_value"]
        return text.data(), text["sh_addr"], syms


def rendezvous_reached(obj, syms, name):
    """Gate 2: the function stores an S-register to [sp,#k] and reloads it."""
    objdump = shutil.which("arm-none-eabi-objdump")
    if objdump is None:
        fail("arm-none-eabi-objdump not found")
    lo = syms[name] & ~1
    hi = min([v & ~1 for v in syms.values() if (v & ~1) > lo] or [lo + 0x1000])
    dis = subprocess.run([objdump, "-d", f"--start-address={lo:#x}",
                          f"--stop-address={hi:#x}", obj],
                         capture_output=True, text=True, check=True).stdout
    st = set(re.findall(r"\bvstr\s+s\d+, \[sp(?:, #(\d+))?\]", dis))
    ld = set(re.findall(r"\bvldr\s+s\d+, \[sp(?:, #(\d+))?\]", dis))
    return bool(st & ld)


STACK_BASE, STACK_SIZE, SP0 = 0x30000, 0x10000, 0x38000
RET = 0x3F000
CALLEE_CORE = [getattr(A, f"UC_ARM_REG_R{i}") for i in range(4, 12)]
S_REGS = [getattr(A, f"UC_ARM_REG_S{i}") for i in range(32)]
R_ARGS = [A.UC_ARM_REG_R0, A.UC_ARM_REG_R1, A.UC_ARM_REG_R2, A.UC_ARM_REG_R3]


def run(text, base, addr, params, args, rng, ret):
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
    stack = rng.randbytes(STACK_SIZE)
    uc.mem_write(STACK_BASE, stack)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    for r in R_ARGS + [A.UC_ARM_REG_R12]:
        uc.reg_write(r, rng.getrandbits(32))
    callee = {r: rng.getrandbits(32) for r in CALLEE_CORE}
    for r, v in callee.items():
        uc.reg_write(r, v)
    s_hi = {}
    for i, r in enumerate(S_REGS):
        v = rng.getrandbits(32)
        uc.reg_write(r, v)
        if i >= 16:
            s_hi[i] = v
    # AAPCS-VFP: f32 args take S0.. in order, i32 args R0.. in order.
    si = ri = 0
    for p, a in zip(params, args):
        if p == "f32":
            uc.reg_write(S_REGS[si], f32_bits(a))
            si += 1
        else:
            uc.reg_write(R_ARGS[ri], a & 0xFFFFFFFF)
            ri += 1
    uc.reg_write(A.UC_ARM_REG_SP, SP0)
    uc.reg_write(A.UC_ARM_REG_LR, RET | 1)
    try:
        uc.emu_start(addr | 1, RET, count=20000)
    except UcError as e:
        return None, f"fault {e} at pc={uc.reg_read(A.UC_ARM_REG_PC):#x}"
    if uc.reg_read(A.UC_ARM_REG_PC) & ~1 != RET:
        return None, "did not return"
    if uc.reg_read(A.UC_ARM_REG_SP) != SP0:
        return None, "SP not restored"
    for i, (r, v) in enumerate(callee.items()):
        if uc.reg_read(r) != v:
            return None, f"callee-saved R{4 + i} clobbered"
    for i, v in s_hi.items():
        if uc.reg_read(S_REGS[i]) & 0xFFFFFFFF != v:
            return None, f"callee-saved S{i} clobbered"
    above = bytes(uc.mem_read(SP0, STACK_BASE + STACK_SIZE - SP0))
    if above != stack[SP0 - STACK_BASE:]:
        return None, "caller's stack above SP written"
    res = A.UC_ARM_REG_R0 if ret == "i32" else A.UC_ARM_REG_S0
    return uc.reg_read(res) & 0xFFFFFFFF, None


def main():
    want_floor, got_floor = expected_emulations(), declared_floor()
    if want_floor != got_floor:
        sys.exit(f"REFUSE: header floor {got_floor} != derived {want_floor} (#1331)")

    eng = wasmtime.Engine()
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, wasmtime.Module.from_file(eng, str(WAT)), [])
    exp = inst.exports(store)

    tmp = tempfile.mkdtemp(prefix="rf1614_")
    checked = bad = 0
    tally = {}
    first = None
    for target in TARGETS:
        for mode in MODES:
            obj, elf = compile_elf(tmp, target, mode)
            text, base, syms = load(elf)
            osyms = load(obj)[2]
            missing = [r for r, _ in ROWS if r not in syms]
            if missing:
                fail(f"[{target}/{mode}] exports missing from the symtab: {missing}")
            for name in sorted(RENDEZVOUS_ROWS):
                if not rendezvous_reached(obj, osyms, name):
                    fail(f"[{target}/{mode}] {name}: no SP-relative vstr/vldr pair — the "
                         "row no longer reaches the f32 rendezvous, so its "
                         "executions would be vacuous")
            print(f"PASS: [{target}/{mode}] {len(ROWS)} exports compiled; "
                  f"{len(RENDEZVOUS_ROWS)} reach the f32 rendezvous")
            rng = random.Random(f"1614/{target}/{mode}")
            for name, params in ROWS:
                for args in grid(params):
                    w = exp[name](store, *[
                        (struct.unpack("<i", struct.pack("<I", a & 0xFFFFFFFF))[0]
                         if p == "i32" else a) for p, a in zip(params, args)])
                    ret = "i32" if name == "brif_i32" else "f32"
                    want = (w & 0xFFFFFFFF) if ret == "i32" else f32_bits(w)
                    for _ in range(STATES):
                        got, err = run(text, base, syms[name], params, args, rng, ret)
                        checked += 1
                        ok = err is None and got == want
                        if not ok:
                            bad += 1
                            why = err or "wrong value"
                            key = (target, mode, name, why.split(" clobbered")[0]
                                   if "clobbered" in why else why)
                            tally[key] = tally.get(key, 0) + 1
                            if first is None:
                                first = (f"[{target}/{mode}] {name}{args}: "
                                         + (err or f"got {got:#010x}, want {want:#010x}"))
    if checked < want_floor:
        fail(f"only {checked} emulations ran, floor {want_floor}")
    if bad:
        for (t, m, n, why), c in sorted(tally.items()):
            print(f"  [{t}/{m}] {n}: {c} x {why}")
        rows = sorted({k[2] for k in tally})
        print(f"rows red: {len(rows)} of {len(ROWS)}: {rows}")
        fail(f"{bad} of {checked} emulations wrong; first: {first}")
    print(f"emulations: {checked}")
    print(f"PASS: {checked} emulations bit-identical to wasmtime with callee-saved "
          "R4..R11 / S16..S31 / SP and the caller's stack intact (garbage "
          "caller-saved registers and stack)")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
