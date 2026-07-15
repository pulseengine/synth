#!/usr/bin/env python3
"""#377 — `--safety-bounds software` optimized-path enforcement differential.

Pre-fix, `--safety-bounds software` emitted NO bounds check on the optimized
codegen path (`ir_to_arm`) — the path that lowers the bulk of a flight loop's
i32 loads/stores. The direct selector emitted the check but its `Bhs
Trap_Handler` resolved to an offset-0 fallthrough in a self-contained image, so
NEITHER path actually trapped. This harness is the value-level gate for both:

  - ELF A: default compile        -> optimized path (asserted via SYNTH_PATH_DEBUG)
  - ELF B: --no-optimize compile  -> direct selector

For each path and each vector, **wasmtime is ground truth**; **unicorn** runs
synth's Thumb-2 output. Vectors cover in-bounds, exact-boundary (must NOT
trap), first-OOB (must trap), far-OOB, and — #752 — the top-of-address-space
wraparound class (`addr >= 2^32 - (offset+size-1)`), where the RETIRED guard
shape ADD-computed the end address mod 2^32 and let the OOB access escape
below the linear-memory base. The shipped guard is the wraparound-safe
SUB-from-bound shape (trap iff `mem_size < k`, else iff
`addr >u mem_size - k`, `k = offset+size`). The inline trap is a `UDF` -> UC_ERR_INSN_INVALID: that IS
the wasm trap (on silicon UsageFault/HardFault). Any OTHER unicorn fault (e.g.
WRITE_UNMAPPED) means an out-of-bounds access was let through — reported as ERR,
never counted as a match. On pre-fix main the OOB vectors FAIL on both paths.

Covers all four optimized-path memory opcodes: MemStore (`st`), MemLoad
(`ld`), MemStoreSubword (`st16`), MemLoadSubword (`ld8`).

Run:
  SYNTH=./target/debug/synth python scripts/repro/safety_bounds_377_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_ERR_INSN_INVALID,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WASM = "scripts/repro/safety_bounds_377.wat"
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

MEM_BYTES = 0x10000  # 1 page = 64 KiB (matches the wat `(memory 1)`)
CODE = 0x00200000
# The optimized path materializes the ABSOLUTE linear-memory base 0x20000100;
# the direct path is R11-relative. Point both at the same window so one
# harness serves both: map the 4 KiB-aligned page below and treat
# LIN = 0x20000100 as byte 0 of linear memory.
LIN_PAGE = 0x20000000
LIN = 0x20000100
STK = 0x30010000
RET = 0x00300000

# (fn, addr, val, expect_trap)
# `st` writes mem[addr+4] (offset=4, size 4): last byte = addr+7.
# `ld` reads mem[addr] (size 4): last byte = addr+3.
# `st16` (size 2): last byte = addr+1. `ld8` (size 1): last byte = addr.
VECTORS = [
    ("st", 100, 0xDEADBEEF, False),            # plain in-bounds
    ("st", MEM_BYTES - 8, 0x11223344, False),  # exact boundary: addr+4+4==size
    ("st", MEM_BYTES - 7, 0x55667788, True),   # first OOB byte -> trap
    ("st", MEM_BYTES, 0x99AABBCC, True),       # addr at size -> trap
    ("st", 2 * MEM_BYTES, 0x0BADF00D, True),   # far OOB -> trap
    ("ld", 200, 0, False),
    ("ld", MEM_BYTES - 4, 0, False),           # exact boundary read
    ("ld", MEM_BYTES - 3, 0, True),            # straddles the end -> trap
    ("ld", 3 * MEM_BYTES, 0, True),            # far OOB -> trap
    ("st16", MEM_BYTES - 2, 0xCAFE, False),    # boundary halfword
    ("st16", MEM_BYTES - 1, 0xBABE, True),     # straddle -> trap
    ("ld8", MEM_BYTES - 1, 0, False),          # last byte readable
    ("ld8", MEM_BYTES, 0, True),               # one past -> trap
    # --- #752: top-of-address-space wraparound class ---
    # The retired guard ADD-computed `addr + offset + size - 1` mod 2^32: for
    # addr >= 2^32 - (offset+size-1) the end address wrapped small, BLO
    # passed, and the access escaped the trap (reading/writing below the
    # linear-memory base). WASM requires a trap on every one of these.
    ("st", 0xFFFFFFF9, 0x752C0DE0, True),      # end 0xFFFFFFF9+7 wraps to 0
    ("st", 0xFFFFFFFC, 0x752C0DE1, True),      # end wraps to 3 (escaped pre-fix)
    ("ld", 0xFFFFFFFC, 0, True),               # the issue's 0xFFFFFFFC size-4 case
    ("ld", 0xFFFFFFFE, 0, True),               # end wraps to 1 (escaped pre-fix)
    ("st16", 0xFFFFFFFF, 0xBEEF, True),        # end wraps to 0 (escaped pre-fix)
    ("ld8", 0xFFFFFFFF, 0, True),              # size-1/offset-0: exact either way
]


def to_i32(x):
    """wasmtime takes SIGNED i32 params; synth vectors are u32 addresses."""
    return x - (1 << 32) if x >= (1 << 31) else x


def pattern():
    return bytes((i * 31 + 7) & 0xFF for i in range(MEM_BYTES))


def compile_elves():
    outs = {}
    for name, extra in (("optimized", []), ("direct", ["--no-optimize"])):
        elf = f"/tmp/sb377_{name}.elf"
        env = dict(os.environ, SYNTH_PATH_DEBUG="1")
        r = subprocess.run(
            [SYNTH, "compile", WASM, "-o", elf, "--target", "cortex-m4",
             "--all-exports", "--safety-bounds", "software"] + extra,
            capture_output=True, text=True, env=env, check=True,
        )
        if name == "optimized" and "optimized (ir_to_arm ok)" not in r.stderr:
            print("ERROR: the 'optimized' ELF did not take the optimized path —"
                  " the #377 gate would be vacuous. stderr:\n" + r.stderr)
            sys.exit(2)
        outs[name] = elf
    return outs


def load_text_and_syms(elf_path):
    f = ELFFile(open(elf_path, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec["sh_type"] == "SHT_SYMTAB":
            for s in sec.iter_symbols():
                if s["st_value"]:
                    syms[s.name] = s["st_value"] & ~1  # clear Thumb bit
    return code, base, syms


def wasmtime_run(module, engine, fn, a, v):
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    mem = inst.exports(store)["memory"]
    mem.write(store, pattern(), 0)
    ret = None
    try:
        if fn.startswith("st"):
            inst.exports(store)[fn](store, to_i32(a), to_i32(v))
        else:
            ret = inst.exports(store)[fn](store, to_i32(a))
        trapped = False
    except wasmtime.Trap:
        trapped = True
    img = bytes(mem.read(store, 0, MEM_BYTES))
    return trapped, ret, img


def unicorn_run(code, base, syms, fn, a, v):
    fa = syms[fn]
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN_PAGE, 0x11000)  # covers LIN..LIN+64K (+0x100 lead-in)
    mu.mem_map(STK - 0x10000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.mem_write(LIN, pattern())
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)        # direct path: linmem base
    mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)  # memory size (bytes) for bounds
    mu.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, v & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + fa - base) | 1, RET, count=100000)
    except UcError as e:
        if e.errno == UC_ERR_INSN_INVALID:
            # UDF: the inline software-bounds trap. Verify it's a real UDF so a
            # stray decode error can't masquerade as a pass.
            pc = mu.reg_read(UC_ARM_REG_PC)
            half = bytes(mu.mem_read(pc, 2))
            if half[1] == 0xDE:  # Thumb UDF #imm8 = 0xDExx
                return True, None, bytes(mu.mem_read(LIN, MEM_BYTES))
        return f"ERR:{e}", None, b""
    ret = mu.reg_read(UC_ARM_REG_R0)
    return False, ret, bytes(mu.mem_read(LIN, MEM_BYTES))


def main():
    elves = compile_elves()
    engine = wasmtime.Engine()
    # wasmtime-py accepts wat text directly (no wabt needed on CI runners).
    module = wasmtime.Module(engine, open(WASM).read())

    total_fails = 0
    for path_name, elf in elves.items():
        code, base, syms = load_text_and_syms(elf)
        print(f"=== {path_name} path ({elf}) ===")
        fails = 0
        for fn, a, v, exp_trap in VECTORS:
            gt_trap, gt_ret, gt_img = wasmtime_run(module, engine, fn, a, v)
            sy_trap, sy_ret, sy_img = unicorn_run(code, base, syms, fn, a, v)
            assert gt_trap == exp_trap, f"vector expectation wrong: {fn}({a})"
            if isinstance(sy_trap, str):
                ok, detail = False, sy_trap
            elif gt_trap:
                ok = bool(sy_trap) and sy_img == gt_img
                detail = f"trap synth={sy_trap} wasmtime={gt_trap}"
            else:
                ok = (not sy_trap) and sy_img == gt_img
                detail = "image identical"
                if fn.startswith("ld") and ok:
                    ok = (sy_ret & 0xFFFFFFFF) == (gt_ret & 0xFFFFFFFF)
                    detail = f"ret synth=0x{sy_ret:08x} wasmtime=0x{gt_ret & 0xFFFFFFFF:08x}"
                elif sy_img != gt_img:
                    d = next(i for i in range(MEM_BYTES) if sy_img[i] != gt_img[i])
                    detail = (f"mem differs @{d}: synth=0x{sy_img[d]:02x} "
                              f"wasmtime=0x{gt_img[d]:02x}")
            fails += 0 if ok else 1
            print(f"  {fn}(addr={a}) trap={exp_trap}: "
                  f"{'OK' if ok else 'MISMATCH'}  [{detail}]")
        print(f"  {len(VECTORS) - fails}/{len(VECTORS)} match on {path_name}\n")
        total_fails += fails
    print("ORACLE: PASS" if total_fails == 0 else f"ORACLE: FAIL ({total_fails})")
    sys.exit(1 if total_fails else 0)


if __name__ == "__main__":
    main()
