#!/usr/bin/env python3
"""#740 — EXECUTION-validate the direct path's wide conditional branches on the
loop-inside-block shape: a `br_if` at a loop head exiting an OUTER block.

Root cause (fixed alongside this harness): the Thumb-2 encoder's 32-bit
B<cond>.W (encoding T3) arm packed `halfword_offset >> 1` into imm6:imm11 —
per ARMv7-M the field value S:J2:J1:imm6:imm11 IS the halfword offset, so
every conditional branch spanning > 254 bytes landed at HALF its intended
displacement. On gust_poll (issue #740) the loop-head empty-budget
`br_if 1 (;@2;)` jumped mid-shape: a spurious state write plus spurious calls
on a round that must not touch memory at all. Narrow (16-bit) B<cond>
encodings were unaffected, which is why the existing short-range CF
differentials (#483/#497/#500/#508/#509) never caught it.

This harness pins the minimal shape (`brif_outer_740.wat`):

  block @1 { block @2 { loop @3 {
      br_if 1 (;@2;)    <- head exit, > 254-byte span -> B<cond>.W
      br_if 2 (;@1;)    <- two-level exit, also wide
      <padding stores>  <- the bytes that force the wide encoding
      br_if 0 (;@3;)    <- back edge
  } } }

with distinct marker stores at each join. The @2 join ends in a NON-TAIL
`return`, so the optimized path declines the function (#500) and it compiles
on the DIRECT selector — the same path gust_poll takes.

Anti-vacuity: the harness FAILS if `poll` contains no 32-bit T3 conditional
branch (e.g. a future codegen change shrinks the function until every branch
encodes narrow) — the fixture must keep exercising the wide encoding to gate
anything.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/brif_outer_740_differential.py
Exits nonzero on any mismatch (return value OR the compared memory window).
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
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

REPO = Path(__file__).resolve().parents[2]
WAT = Path(__file__).with_name("brif_outer_740.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Standalone-image machine state (see the emitted Reset_Handler): 1-page
# linear memory at 0x20000000, r11 = linmem base, r10 = linmem size, r9 =
# globals base (unused by this module but kept mapped), SP above it all.
LIN = 0x2000_0000
LIN_SIZE = 0x1_0000
CODE = 0x0
SP_INIT = LIN + 0x2_0000

MEM_WINDOW = 0x100  # bytes of linear memory compared after each call

# (x0, x1) argument pairs.
#   x1 == 0        -> the loop-head `br_if 1` (the #740 edge) is TAKEN
#   x0 >= 100      -> the two-level `br_if 2` is taken on the first iteration
#   otherwise      -> the loop runs x1 times and falls through to the @2 join
CASES = [
    (7, 0),  # head exit taken immediately — the exact #740 shape
    (200, 0),  # head exit taken before the bounds exit is even tested
    (200, 1),  # two-level bounds exit taken (the second wide branch)
    (5, 1),  # one full loop iteration, fall-through join
    (5, 3),  # several iterations
    (99, 6),  # bounds-exit boundary value, never taken
]


def compile_image(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text").data()
    lin = f.get_section_by_name(".linear_memory")
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for s in sec.iter_symbols():
                if s.name:
                    syms[s.name] = s["st_value"]
    return text, lin.data() if lin else b"", syms


def has_wide_cond_branch(text, start, size):
    """True if [start, start+size) contains a 32-bit T3 conditional branch:
    hw1 = 1111 0 S cond(4) imm6 with cond != 111x, hw2 = 10 J1 0 J2 imm11."""
    off = start
    end = min(start + size, len(text))
    while off + 4 <= end:
        hw1 = int.from_bytes(text[off:off + 2], "little")
        wide = (hw1 & 0xE000) == 0xE000 and (hw1 & 0x1800) != 0
        if (hw1 & 0xF800) == 0xF000:
            hw2 = int.from_bytes(text[off + 2:off + 4], "little")
            cond = (hw1 >> 6) & 0xF
            if (hw2 & 0xD000) == 0x8000 and cond < 0xE:
                return True
        off += 4 if wide else 2
    return False


def wasmtime_poll(x0, x1):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    mem = inst.exports(st)["memory"]
    r = inst.exports(st)["poll"](st, x0, x1)
    return r & 0xFFFFFFFF, bytes(mem.read(st, 0, MEM_WINDOW))


def unicorn_poll(text, lin_init, faddr, x0, x1):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x2_0000)
    mu.mem_write(CODE, text)
    if lin_init:
        mu.mem_write(LIN, lin_init[:LIN_SIZE])
    mu.reg_write(UC_ARM_REG_R9, LIN + LIN_SIZE)  # globals base (unused, mapped)
    mu.reg_write(UC_ARM_REG_R10, LIN_SIZE)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_SP, SP_INIT)
    ret = CODE + 0xFF00
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.reg_write(UC_ARM_REG_R0, x0)
    mu.reg_write(UC_ARM_REG_R1, x1)
    try:
        mu.emu_start((faddr & ~1) | 1, ret, timeout=5_000_000, count=200_000)
    except UcError as e:
        return f"ERR:{e}", None
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF, bytes(mu.mem_read(LIN, MEM_WINDOW))


def main():
    out = "/tmp/brif_outer_740.elf"
    compile_image(out)
    text, lin_init, syms = load(out)
    if "poll" not in syms:
        sys.exit("FAIL: symbol 'poll' missing from the compiled image")
    faddr = syms["poll"] & ~1

    # Anti-vacuity: the fixture only gates #740 while its exits actually
    # encode as 32-bit B<cond>.W. A poll body of 258+ bytes guarantees the
    # head exit's span; assert the wide encoding is really present.
    fsize = next(
        (s["st_size"] for sec in ELFFile(open(out, "rb")).iter_sections()
         if sec.header.sh_type == "SHT_SYMTAB"
         for s in sec.iter_symbols() if s.name == "poll"),
        0,
    )
    if not has_wide_cond_branch(text, faddr, fsize or 0x400):
        print("FAIL: no 32-bit B<cond>.W (T3) conditional branch found in "
              "'poll' — the fixture no longer exercises the #740 wide "
              "encoding; grow the padding body")
        sys.exit(1)
    print("OK  engagement: 'poll' contains a wide (T3) conditional branch")

    fails = 0
    for x0, x1 in CASES:
        gt_ret, gt_mem = wasmtime_poll(x0, x1)
        lin = bytearray(lin_init) if lin_init else bytearray(LIN_SIZE)
        got_ret, got_mem = unicorn_poll(text, bytes(lin), faddr, x0, x1)
        ok = got_ret == gt_ret and got_mem == gt_mem
        fails += 0 if ok else 1
        tag = f"0x{got_ret:08X}" if isinstance(got_ret, int) else got_ret
        memtag = "mem==" if got_mem == gt_mem else "mem!="
        print(f"{'OK  ' if ok else 'FAIL'} poll({x0:>3},{x1}) = {tag} "
              f"(wasmtime 0x{gt_ret:08X}) {memtag}")
        if not ok and got_mem is not None and got_mem != gt_mem:
            diffs = [i for i in range(MEM_WINDOW) if got_mem[i] != gt_mem[i]]
            print(f"      first divergent bytes at offsets: {diffs[:8]}")

    print("\nRESULT:", "PASS" if not fails else f"FAIL ({fails} mismatches)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
