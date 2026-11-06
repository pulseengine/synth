#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 87
"""#1642 — an out-of-bounds `f64.store` must write NOTHING before it traps.

The defect (live on main c20d37b2, found by the #1636 spec-execution runner,
`memory_trap.wast` 269/282): under `--safety-bounds software`, cortex-m7dp
lowered `f64.store` as `VMOV lo, hi, Dm` then two 4-byte integer stores, EACH
behind its own bounds guard — the lo word's guard checked `offset+4`, the hi
word's `offset+8`. An access straddling the end of memory therefore wrote its
low word, and only then trapped on the hi word's guard. The WebAssembly spec
traps a store as an effect of executing it: a trapping store writes nothing.
The fix guards ALL 8 bytes once, before either word is written (the shape
`i64.store` already had).

What this oracle executes, for each leg, against wasmtime as ground truth:

  * `st`     f64.store offset=0     — in-bounds, the exact boundary (size-8,
                                      must NOT trap), every straddle size-7 ..
                                      size-1, fully out of bounds, and the #752
                                      top-of-address-space wraparound class;
  * `st_o4`  f64.store offset=4     — the straddle reached through the memarg
                                      offset;
  * `st_big` f64.store offset=4096  — an offset past the SUBW imm12 reach, so
                                      the guard materializes its constant
                                      (MOVW path);
  * `ld`     f64.load               — CONTROL: a split load that traps on its
                                      second guard has no side effect, so it
                                      was never wrong; executed to show that;
  * `st64`   i64.store              — CONTROL: already checked once.

Every vector compares the TRAP and the WHOLE linear-memory image (plus the page
after it, so an escaping write is visible), and loads compare the 64-bit result
bit-exactly. Each stored value is chosen per vector so that EVERY one of its 8
bytes differs from the prefill byte it lands on — a partial write can never
coincide with the untouched image.

Legs — cortex-m7dp is the only ARM target that accepts scalar f64 (#369); every
f64 function takes the DIRECT selector on all three invocations (the optimized
path declines float ops, #120), so the three legs are three images of the same
lowering, executed separately because the images differ:
  self-contained (`--all-exports`), `--relocatable`, `--no-optimize`.
Plus the honest-decline pin: `--safety-bounds mask` still REFUSES the f64
functions (the decline is unchanged by this fix; it is not new reach).

Out of scope, measured when the lane was scoped: RV32 has no f64 (declined),
its i64.store is guarded once (and clamped once under mask); AArch64 stores an
f64 with one `str d` behind one guard; memory.fill/copy guard the whole range
before the loop.

Red on c20d37b2 (the pre-fix binary): 8 vectors per leg = 24 mismatches, each
"trap, but memory differs" on the straddled low word. Green on the fix.

Run:
  SYNTH=./target/debug/synth python3 scripts/repro/f64_store_partial_1642_differential.py
Exits nonzero on any mismatch.
"""

import os
import struct
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

WAT = """
(module
  (memory (export "memory") 1)
  (func (export "st") (param i32 f64) (f64.store (local.get 0) (local.get 1)))
  (func (export "st_o4") (param i32 f64)
    (f64.store offset=4 (local.get 0) (local.get 1)))
  (func (export "st_big") (param i32 f64)
    (f64.store offset=4096 (local.get 0) (local.get 1)))
  (func (export "ld") (param i32) (result f64) (f64.load (local.get 0)))
  (func (export "st64") (param i32 i64) (i64.store (local.get 0) (local.get 1))))
"""

MEM = 0x10000  # (memory 1)
CODE = 0x00200000
LIN = 0x20000000  # R11 linear-memory base
TAIL = 0x1000  # one mapped page AFTER memory: an escaping write lands here
STK = 0x30010000
RET = 0x00300000

OFFSET = {"st": 0, "st_o4": 4, "st_big": 4096, "ld": 0, "st64": 0}

# (fn, addr, expect_trap)
VECTORS = [
    ("st", 100, False),
    ("st", MEM - 8, False),  # exact boundary: addr+8 == size
    *[("st", MEM - k, True) for k in range(7, 0, -1)],  # straddles
    ("st", MEM, True),  # fully out of bounds
    ("st", 2 * MEM, True),
    ("st", 0xFFFFFFF9, True),  # #752 wraparound class
    ("st", 0xFFFFFFFC, True),
    ("st", 0xFFFFFFFF, True),
    ("st_o4", MEM - 12, False),  # boundary through the offset
    ("st_o4", MEM - 11, True),  # straddle: lo word in bounds
    ("st_o4", MEM - 8, True),  # straddle: lo word exactly the last word
    ("st_o4", MEM - 7, True),  # lo word itself straddles
    ("st_o4", MEM - 4, True),  # fully out of bounds
    ("st_o4", 0xFFFFFFFC, True),
    ("st_big", MEM - 4096 - 8, False),  # boundary, MOVW-materialized guard
    ("st_big", MEM - 4096 - 7, True),
    ("st_big", MEM - 4096 - 4, True),
    ("st_big", MEM - 4096, True),
    ("ld", MEM - 8, False),  # control
    ("ld", MEM - 4, True),
    ("ld", MEM, True),
    ("st64", MEM - 8, False),  # control
    ("st64", MEM - 4, True),
]

LEGS = [
    ("self-contained", ["--all-exports"]),
    ("relocatable", ["--relocatable"]),
    ("no-optimize", ["--all-exports", "--no-optimize"]),
]


def pattern():
    return bytes((i * 31 + 7) & 0xFF for i in range(MEM))


PAT = pattern()


def value_bits(fn, addr):
    """8 bytes, each differing from the prefill byte it would land on; bit 62
    cleared so the f64 is never a NaN (whose payload a float round-trip could
    canonicalize). Bytes landing outside memory still get a defined value."""
    ea = (addr + OFFSET[fn]) & 0xFFFFFFFF
    b = bytearray()
    for k in range(8):
        a = ea + k
        p = PAT[a] if a < MEM else 0x3C
        b.append(~p & 0xFF)
    b[7] &= 0xBF  # bit 62 (exponent MSB) cleared -> finite, not NaN
    return struct.unpack("<Q", bytes(b))[0]


def to_i32(x):
    return x - (1 << 32) if x >= (1 << 31) else x


def to_i64(x):
    return x - (1 << 64) if x >= (1 << 63) else x


def compile_leg(src, out, extra, bounds="software"):
    r = subprocess.run(
        [SYNTH, "compile", src, "-o", out, "-b", "arm", "--target", "cortex-m7dp",
         "--safety-bounds", bounds, *extra],
        capture_output=True, text=True,
    )
    return r.returncode, r.stdout + r.stderr


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec["sh_type"] == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for s in sec.iter_symbols():
                if s.name and s["st_info"]["type"] == "STT_FUNC":
                    syms[s.name] = s["st_value"] & ~1
    return code, base, syms


def wasmtime_run(module, engine, fn, addr):
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    ex = inst.exports(store)
    mem = ex["memory"]
    mem.write(store, PAT, 0)
    ret = None
    v = value_bits(fn, addr)
    try:
        if fn == "ld":
            r = ex[fn](store, to_i32(addr))
            ret = struct.unpack("<Q", struct.pack("<d", r))[0]
        elif fn == "st64":
            ex[fn](store, to_i32(addr), to_i64(v))
        else:
            ex[fn](store, to_i32(addr), struct.unpack("<d", struct.pack("<Q", v))[0])
        trapped = False
    except wasmtime.Trap:
        trapped = True
    return trapped, ret, bytes(mem.read(store, 0, MEM))


def unicorn_run(code, base, syms, fn, addr):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    try:
        from unicorn.arm_const import UC_CPU_ARM_MAX
        uc.ctl_set_cpu_model(UC_CPU_ARM_MAX)
    except (ImportError, AttributeError):
        pass
    uc.mem_map(CODE, (len(code) + 0xFFF) & ~0xFFF or 0x1000)
    uc.mem_write(CODE, code)
    uc.mem_map(LIN, MEM + TAIL)
    uc.mem_write(LIN, PAT + bytes([0x3C]) * TAIL)
    uc.mem_map(STK - 0x10000, 0x10000)
    uc.mem_map(RET, 0x1000)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    uc.reg_write(UC_ARM_REG_SP, STK)
    uc.reg_write(UC_ARM_REG_R11, LIN)
    uc.reg_write(UC_ARM_REG_R10, MEM)
    uc.reg_write(UC_ARM_REG_R0, addr & 0xFFFFFFFF)
    v = value_bits(fn, addr)
    if fn == "st64":  # AAPCS: i64 after an i32 sits in the even pair r2:r3
        uc.reg_write(UC_ARM_REG_R2, v & 0xFFFFFFFF)
        uc.reg_write(UC_ARM_REG_R3, v >> 32)
    elif fn != "ld":
        uc.reg_write(UC_ARM_REG_D0, v)
    uc.reg_write(UC_ARM_REG_LR, RET | 1)
    entry = CODE + syms[fn] - base
    trapped = False
    try:
        uc.emu_start(entry | 1, RET, count=10000)
    except UcError as e:
        pc = uc.reg_read(UC_ARM_REG_PC)
        off = pc - CODE
        if 0 <= off < len(code) - 1 and code[off + 1] == 0xDE:  # Thumb UDF #imm8
            trapped = True
        else:
            return f"ERR:{e} at pc={pc:#x} (not the inline UDF trap)", None, b"", b""
    img = bytes(uc.mem_read(LIN, MEM))
    tail = bytes(uc.mem_read(LIN + MEM, TAIL))
    ret = None if trapped or fn != "ld" else uc.reg_read(UC_ARM_REG_D0)
    return trapped, ret, img, tail


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT)
    tmp = tempfile.mkdtemp(prefix="f64st1642_")
    src = os.path.join(tmp, "f64_store_1642.wat")
    with open(src, "w") as fh:
        fh.write(WAT)

    total = fails = 0
    for leg, extra in LEGS:
        elf = os.path.join(tmp, f"{leg}.o")
        rc, log = compile_leg(src, elf, extra)
        if rc != 0 or "skipped" in log:
            print(f"FAIL [{leg}]: compile rc={rc} or a function was skipped:\n{log}")
            sys.exit(2)
        code, base, syms = load(elf)
        missing = [f for f in OFFSET if f not in syms]
        if missing:
            print(f"FAIL [{leg}]: symbols missing from the image: {missing}")
            sys.exit(2)
        leg_fails = 0
        for fn, addr, exp_trap in VECTORS:
            gt_trap, gt_ret, gt_img = wasmtime_run(module, engine, fn, addr)
            assert gt_trap == exp_trap, f"vector expectation wrong: {fn}({addr:#x})"
            sy_trap, sy_ret, sy_img, sy_tail = unicorn_run(code, base, syms, fn, addr)
            total += 1
            if isinstance(sy_trap, str):
                ok, detail = False, sy_trap
            elif sy_trap != gt_trap:
                ok, detail = False, f"trap synth={sy_trap} wasmtime={gt_trap}"
            elif sy_tail != bytes([0x3C]) * TAIL:
                ok, detail = False, "a write ESCAPED past the end of memory"
            elif sy_img != gt_img:
                d = [i for i in range(MEM) if sy_img[i] != gt_img[i]]
                ok = False
                detail = (f"trap={sy_trap}, memory differs at {len(d)} byte(s) "
                          f"{d[0]:#x}..{d[-1]:#x} (a PARTIAL WRITE)")
            elif fn == "ld" and not gt_trap and sy_ret != gt_ret:
                ok, detail = False, f"ld result synth={sy_ret:#018x} wasmtime={gt_ret:#018x}"
            else:
                ok, detail = True, ("trap, memory unchanged" if gt_trap
                                    else "no trap, image identical")
            leg_fails += 0 if ok else 1
            print(f"  [{leg}] {fn}(addr={addr:#x}) expect_trap={exp_trap}: "
                  f"{'OK' if ok else 'MISMATCH'}  [{detail}]")
        print(f"[{leg}] {len(VECTORS) - leg_fails}/{len(VECTORS)} match\n")
        fails += leg_fails

    # The decline pin: `mask` still refuses the f64 memory functions — the
    # fix does not lift it (that would be new reach needing its own oracle).
    rc, log = compile_leg(src, os.path.join(tmp, "mask.o"), ["--relocatable"], "mask")
    declined = ("f64.store under --safety-bounds" in log
                and "f64.load under --safety-bounds" in log)
    print(f"[mask] f64.store/f64.load decline: {'PINNED' if declined else 'MOVED'}")
    if not declined:
        print(log)
        fails += 1

    print(f"#1642 EMULATED={total} MISMATCHES={fails}")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
