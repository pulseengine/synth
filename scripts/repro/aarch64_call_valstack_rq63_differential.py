#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 13
"""RQ-63-A64STACK — aarch64 call value-stack execution differential: unicorn
vs wasmtime, with a temp-clobbering callee and non-contract register canaries.

THE CONSTRAINT THIS ORACLE GATES. Every aarch64 value-stack entry lives in a
caller-saved temp (x9..x15 GP, v16..v23 FP), and a `bl`/`blr` may clobber all
of them. Until v0.63 the selector therefore required the value stack to hold
EXACTLY the callee's arguments at a `call` / `call_indirect` and LOUD-DECLINED
otherwise:

    call to function N: value stack holds N entries but needs exactly N (call
    clobbers caller-saved temps below the args); loud-declining (#851)

Measured (RQ-62-REACH's census, re-run at this lane's base): that ONE message
is the modal per-function decline behind 77 of the 197 aarch64 corpus
declines — 35 core + 42 component modules, 4,468 direct-call + 81
call_indirect skips — because it refuses every `(binop a (call ..))`,
`(call g a (call f ..))` and `(store addr (call ..))` a real compiler emits.
The v0.63 lowering SPILLS the entries below the args to a 16-byte-aligned SP
area around the call and reloads them into the SAME registers before the
result is moved out of x0.

WHAT THIS HARNESS PROVES, and why each part can fail:

  * RED FIRST: on the pre-lane compiler every shape in the fixture DECLINES,
    so the harness exits non-zero at the compile step — it cannot go green
    without the lowering.
  * wasmtime FIRST: every expected value comes from wasmtime executing the
    same module with the same host function; no expected value is written
    here.
  * THE CALLEE CLOBBERS EVERY TEMP. The imported `clobber_add` (hand-encoded,
    verified against clang) overwrites x9..x17 and v16..v23 with named
    canaries BEFORE computing a+b. A synth-compiled callee happens to touch
    only the temps it needs, so a missing reload could pass by luck; against
    this callee a missing or wrong reload is a WRONG VALUE — and when the
    returned value IS one of the canaries the harness names the register
    ("REGISTER DEFECT"), the #1021 expansion-canary discipline.
  * NON-CONTRACT REGISTERS ARE CANARIED (the #1093 lesson on this backend: a
    value-stack defect returns an uninitialised register, it does not crash).
    Every GP register the ABI does not assign (x9..x17, x19..x27) is seeded
    with 0xC0DE0000|index; after each run the callee-saved x19..x28 and SP
    must be exactly as seeded — a spill area that is not released, or a stray
    write to a callee-saved register, is a register defect even when x0 is
    right.
  * BOTH REGISTER FILES AND WIDTHS: an f64 sits below the call in one shape
    (spilled via `str d`), an i64 in another (the 64-bit spill width), three
    values in a third (an odd count — the area pads to 16 bytes).
  * THE TRAP DIRECTION STAYS: a `call_indirect` with a live value below its
    args must still trap on an out-of-range index exactly where wasmtime does.
  * DECLINE HONESTY STAYS: a float-result callee, a >8-arg callee, and the
    #1093 PARAMETER-taking block type must still refuse cleanly — exit != 0,
    no panic, the named needle, NO object written. That half emulates
    nothing, so the `# ci-checks: emulations` floor cannot see it; it carries
    its own `refusals` floor here, mirrored by a grep in ci.yml.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_call_valstack_rq63_differential.py
"""

import os
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn import arm64_const as A

HERE = Path(__file__).parent
WAT = HERE / "aarch64_call_valstack_rq63.wat"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, STK, RET = 0x100000, 0x200000, 0x300000
LINMEM = 0x1000000  # x28 — the linear-memory base precondition (#851)
LINMEM_SIZE = 0x10000  # the fixture declares (memory 1) = 64 KiB
M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
TRAP = "TRAP"

R_AARCH64_ADR_PREL_PG_HI21 = 275
R_AARCH64_ADD_ABS_LO12_NC = 277
R_AARCH64_JUMP26 = 282
R_AARCH64_CALL26 = 283

# clobber_add(a, b) = a + b — but it FIRST overwrites every value-stack temp
# (x9..x15, v16..v23) and both IP registers with named canaries. Hand-encoded;
# verified against `clang -target arm64-apple-macos -c` of the same body:
#   movz x9,#0xC109 ... movz x17,#0xC111 ; fmov d16,x9 ... fmov d23,x16 ;
#   add w0,w0,w1 ; ret
HOST_DEFS = {
    "clobber_add": [
        0xD2982129, 0xD298214A, 0xD298216B, 0xD298218C, 0xD29821AD,
        0xD29821CE, 0xD29821EF, 0xD2982210, 0xD2982231,
        0x9E670130, 0x9E670151, 0x9E670172, 0x9E670193,
        0x9E6701B4, 0x9E6701D5, 0x9E6701F6, 0x9E670217,
        0x0B010000, 0xD65F03C0,
    ],
}
# The value the callee leaves in each temp -> the register's name.
CLOBBER_CANARIES = {0xC109 + i: f"x{9 + i}" for i in range(9)}


def canary(i):
    return 0xC0DE0000 | i


GP_REGS = {i: getattr(A, f"UC_ARM64_REG_X{i}") for i in range(0, 29)}
# Seeded before every run: every GP register the ABI assigns nothing to.
SEEDED = list(range(9, 18)) + list(range(19, 28))
SEED_CANARIES = {canary(i): f"x{i}" for i in SEEDED}

# (entry, args, i64-wide?, why). Expected values come from wasmtime, never here.
CASES = [
    ("below_local", [3, 4], False,
     "a + inc7(b): one GP value below a LOCAL direct call"),
    ("below_local", [0xFFFFFFFF, 1], False,
     "same shape, wrapping through the add"),
    ("below_import", [10, 20], False,
     "a + clobber_add(b,100): below an IMPORT that clobbers every temp"),
    ("nested_arg", [50, 7], False,
     "sub(a, clobber_add(b,1)): a call as the SECOND argument of a call"),
    ("two_calls", [9, 4], False,
     "sub(clobber_add(a,1), clobber_add(b,2)): the first result survives the second call"),
    ("deep3", [2, 3, 50], False,
     "a + b*(c - clobber_add(a,b)): THREE values below (odd count, padded area)"),
    ("deep3", [0xFFFFFFFF, 2, 1], False,
     "same shape, wrapping"),
    ("below_i64", [0x1_0000_0005, 0x8000_0000], True,
     "a + dbl64(b): an i64 below the call (64-bit spill width)"),
    ("below_fp", [10], False,
     "trunc(2.5 + f64(clobber_add(x,1))): an f64 below the call (str d / ldr d)"),
    ("store_below", [16, 5], False,
     "store ADDRESS below the stored call result, read back through memory"),
    ("below_indirect", [100, 3, 0], False,
     "a + call_indirect(b)[slot 0]: a value below a call_indirect's args"),
    ("below_indirect", [100, 3, 1], False,
     "index 1 is out of range: must still TRAP with a live value pending"),
    ("below_block", [1, 2], False,
     "a + block(result i32){ clobber_add(b,5) }: the call inside a value-carrying frame"),
]

# (name, module, needle) — must STILL refuse after the lowering.
REFUSALS = [
    ("float-result callee", """(module
  (func $fr (result f64) (f64.const 1.0))
  (func (export "c") (result i32) (i32.trunc_f64_s (call $fr))))""",
     "float result"),
    ("nine-argument callee", """(module
  (func $nine (param i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
    (local.get 8))
  (func (export "c") (param i32) (result i32)
    (call $nine (local.get 0) (local.get 0) (local.get 0) (local.get 0)
                (local.get 0) (local.get 0) (local.get 0) (local.get 0)
                (local.get 0))))""",
     "at most 8 register"),
    ("#1093 PARAMETER-taking block type", """(module
  (func (export "c") (param i32) (result i32)
    (local.get 0)
    (if (param i32) (result i32) (local.get 0)
      (then (i32.add (i32.const 1)))
      (else (i32.add (i32.const 2))))))""",
     "PARAMETER-taking block type"),
]


def wasmtime_run(fn, args, is64):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    linker = wasmtime.Linker(engine)
    i32 = wasmtime.ValType.i32()
    linker.define_func("env", "clobber_add",
                       wasmtime.FuncType([i32, i32], [i32]),
                       lambda a, b: (a + b) & M32)
    f = linker.instantiate(store, module).exports(store)[fn]
    if is64:
        conv = [struct.unpack("<q", struct.pack("<Q", a & M64))[0] for a in args]
    else:
        conv = [struct.unpack("<i", struct.pack("<I", a & M32))[0] for a in args]
    try:
        r = f(store, *conv)
    except wasmtime.Trap:
        return TRAP
    return r & (M64 if is64 else M32)


def compile_aarch64(wat, out):
    cmd = [SYNTH, "compile", str(wat), "-o", out, "-b", "aarch64",
           "--all-exports", "--relocatable"]
    return subprocess.run(cmd, capture_output=True, text=True,
                          env={"PATH": "/usr/bin:/bin"})


def load_link_with_host(path):
    """Place `.text` at CODE, append the harness's OWN definition of the
    imported function after it, and resolve every relocation — the undefined
    external resolves to the harness definition, exactly what a host linker
    does (the #1017 contract)."""
    f = ELFFile(open(path, "rb"))
    sections = list(f.iter_sections())
    text_sec = f.get_section_by_name(".text")
    text = bytearray(text_sec.data())
    text_idx = sections.index(text_sec)

    host_addr = {}
    for name, words in HOST_DEFS.items():
        host_addr[name] = CODE + len(text)
        for w in words:
            text += struct.pack("<I", w)

    sym_addr, by_name = {}, {}
    for i, sy in enumerate(f.get_section_by_name(".symtab").iter_symbols()):
        if sy["st_shndx"] == text_idx:
            a = CODE + sy["st_value"]
        elif sy["st_shndx"] == "SHN_UNDEF" and sy.name in host_addr:
            a = host_addr[sy.name]
        else:
            continue
        sym_addr[i] = a
        if sy.name:
            by_name.setdefault(sy.name, a)

    rela = f.get_section_by_name(".rela.text")
    applied = 0
    if rela is not None:
        for r in rela.iter_relocations():
            r_off = r["r_offset"]
            r_type = r["r_info_type"]
            target = sym_addr.get(r["r_info"] >> 32)
            if target is None:
                sys.exit(f"relocation against unplaced symbol "
                         f"(index {r['r_info'] >> 32})")
            site = CODE + r_off
            word = struct.unpack_from("<I", text, r_off)[0]
            s = target + r["r_addend"]
            if r_type in (R_AARCH64_CALL26, R_AARCH64_JUMP26):
                word = (word & 0xFC000000) | (((s - site) // 4) & 0x03FFFFFF)
            elif r_type == R_AARCH64_ADR_PREL_PG_HI21:
                v = ((s >> 12) - (site >> 12)) & 0x1FFFFF
                word &= ~((0x3 << 29) | (0x7FFFF << 5))
                word |= (v & 0x3) << 29
                word |= ((v >> 2) & 0x7FFFF) << 5
            elif r_type == R_AARCH64_ADD_ABS_LO12_NC:
                word = (word & ~(0xFFF << 10)) | ((s & 0xFFF) << 10)
            else:
                sys.exit(f"unexpected relocation type {r_type}")
            struct.pack_into("<I", text, r_off, word)
            applied += 1
    if applied == 0:
        sys.exit("no relocations applied — every call would be a self-branch "
                 "and the clobber claim would go untested")
    print(f"  [{applied} relocations applied; host clobber_add appended]")
    return bytes(text), by_name


def emu_run(code, faddr, args, is64):
    """Run `faddr(*args)`; returns (result-or-TRAP, register-defect list)."""
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_map(LINMEM, LINMEM_SIZE)
    mu.mem_write(CODE, code)
    mu.reg_write(A.UC_ARM64_REG_SP, STK)
    mu.reg_write(A.UC_ARM64_REG_LR, RET)
    mu.reg_write(A.UC_ARM64_REG_X28, LINMEM)
    for i in SEEDED:
        mu.reg_write(GP_REGS[i], canary(i))
    mask = M64 if is64 else M32
    for i, a in enumerate(args):
        mu.reg_write(GP_REGS[i], a & mask)
    try:
        mu.emu_start(faddr, RET, count=100000)
    except UcError:
        return TRAP, []  # the guarded `brk #0`
    got = mu.reg_read(A.UC_ARM64_REG_X0) & mask
    bad = []
    for i in range(19, 28):
        v = mu.reg_read(GP_REGS[i])
        if v != canary(i):
            bad.append(f"callee-saved x{i} = {v:#x}, seeded {canary(i):#x}")
    v = mu.reg_read(A.UC_ARM64_REG_X28)
    if v != LINMEM:
        bad.append(f"x28 (linear-memory base) = {v:#x}, entered {LINMEM:#x}")
    v = mu.reg_read(A.UC_ARM64_REG_SP)
    if v != STK:
        bad.append(f"sp = {v:#x} after return, entered {STK:#x} — "
                   f"a spill area was not released")
    return got, bad


def diagnose(got):
    """Name the register when a wrong result IS a canary."""
    if got in SEED_CANARIES:
        return (f"REGISTER DEFECT: the result is the harness's seed for "
                f"{SEED_CANARIES[got]} — an uninitialised register was returned")
    if got in CLOBBER_CANARIES:
        return (f"REGISTER DEFECT: the result is what the callee left in "
                f"{CLOBBER_CANARIES[got]} — the post-call reload is missing")
    return "wrong value (not a canary)"


def refusal_probe(name, wat, needle):
    tmp = tempfile.mkdtemp()
    wat_path = os.path.join(tmp, "probe.wat")
    obj_path = os.path.join(tmp, "probe.o")
    with open(wat_path, "w") as w:
        w.write(wat)
    r = compile_aarch64(wat_path, obj_path)
    err = r.stdout + r.stderr
    wrote = os.path.exists(obj_path) and os.path.getsize(obj_path) > 0
    ok = True
    if r.returncode == 0:
        print(f"  FAIL {name}: compiled — the refusal was relaxed")
        ok = False
    if "panicked at" in err or "RUST_BACKTRACE" in err:
        print(f"  FAIL {name}: panicked instead of declining cleanly:\n{err}")
        ok = False
    if needle not in err:
        print(f"  FAIL {name}: refusal does not carry the needle "
              f"{needle!r}:\n{err}")
        ok = False
    if wrote:
        print(f"  FAIL {name}: an object was written despite the refusal")
        ok = False
    shutil.rmtree(tmp, ignore_errors=True)
    if ok:
        print(f"  ok   {name}: still refuses (exit {r.returncode}, "
              f"needle present, no object)")
    return ok


def main():
    tmp = tempfile.mkdtemp()
    obj = os.path.join(tmp, "a64stack.o")
    r = compile_aarch64(WAT, obj)
    if r.returncode != 0 or "skipping" in r.stderr:
        print(f"RED: aarch64 compile of {WAT.name} declined/failed — the "
              f"call value-stack lowering is absent (pre-RQ-63-A64STACK "
              f"compiler?):\n{r.stdout}\n{r.stderr}")
        return 1
    print("== link (host clobber_add appended, relocations applied) ==")
    code, syms = load_link_with_host(obj)

    print("== execution differential (wasmtime first; callee clobbers every "
          "temp; non-contract registers canaried) ==")
    fails = executions = value_cases = trap_cases = cs_checks = 0
    for fn, args, is64, why in CASES:
        want = wasmtime_run(fn, args, is64)
        got, bad = emu_run(code, syms[fn], args, is64)
        executions += 1
        if want == TRAP:
            trap_cases += 1
        else:
            value_cases += 1
        if got != TRAP:
            cs_checks += 1
        ok = got == want and not bad
        show = (lambda v: v if v == TRAP else f"{v:#x}")
        print(f"  {'ok  ' if ok else 'FAIL'} {fn}{tuple(args)} -> {show(got)} "
              f"(wasmtime: {show(want)}) — {why}")
        if got != want and got != TRAP:
            print(f"       {diagnose(got)}")
        for b in bad:
            print(f"       REGISTER DEFECT: {b}")
        if not ok:
            fails += 1

    if trap_cases == 0 or value_cases == 0:
        print(f"VACUOUS: trap_cases={trap_cases} value_cases={value_cases}")
        return 1
    if cs_checks == 0:
        print("VACUOUS: no callee-saved/SP check ran")
        return 1

    print("== decline honesty ==")
    refusals = 0
    for name, wat, needle in REFUSALS:
        if refusal_probe(name, wat, needle):
            refusals += 1
        else:
            fails += 1
    if refusals == 0:
        print("VACUOUS: refusals=0 — the decline-honesty half asserted nothing")
        return 1

    # `synth compile` writes a sidecar beside the object, so remove the tree.
    shutil.rmtree(tmp, ignore_errors=True)
    print(f"\nrefusals: {refusals}")
    print(f"callee-saved checks: {cs_checks}")
    print(f"executions: {executions} ({value_cases} value, {trap_cases} trap)")
    if fails:
        print(f"RESULT: FAIL ({fails})")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
