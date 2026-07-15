#!/usr/bin/env python3
"""#406 / #739-cluster COVERAGE WIDENER — multi-chunk / multi-segment static
data across BOTH the self-contained (`--cortex-m`, no --relocatable) and the
`--relocatable` object paths, with segments at varied offsets: a low segment, an
UNALIGNED segment that STRADDLES a 4 KiB internal page boundary (0x1000), an
overlapping pair (in-order "later wins"), a HIGH segment near the top of a two-
page linear memory (0x1FF0 — approaching the globals-table boundary the self-
contained image lays out just above linmem), and a long multi-word segment that
forces a multi-word ROM->RAM copy.

WHY BOTH PATHS
  - Self-contained: the discriminating check. RAM is mapped ZEROED; whatever
    ends up in linear memory is ONLY what the artifact's OWN Reset_Handler
    copied there (ROM->RAM crt0 `.data` init). A dropped/short/mis-based copy
    (the #758/#746/#739 failure family) reads 0 or garbage and diverges. This
    is the path where the coverage bites.
  - Relocatable: the addressing check. Memory 0 lives at the runtime R11 base
    and the embedder populates its init segments (the object carries no ROM
    image on this path). The harness maps memory 0 at R11 and writes the wasm
    init image itself (the embedder's contract), then verifies every load's
    ADDRESS arithmetic (R11 + offset, incl. the straddle and high-offset cases)
    matches wasmtime. It cannot catch a dropped copy (there is none on this
    path) — it catches a mis-computed offset.

ANTI-VACUOUS
  Ground truth is wasmtime (not a re-derivation of synth's own output). The
  self-contained side executes the REAL reset path on ZEROED RAM, so a compiler
  that ships no init data goes RED (reads 0). The relocatable side maps .text at
  a base far from the R11 memory base so any baked-absolute static offset lands
  in unmapped space (fault) rather than accidentally resolving.

NOTE — this WIDENS coverage. It does NOT claim the #757 cluster closed (#757
stays OPEN, blocked on the reporter's reduced module). If a case diverges, that
is a real find to report LOUDLY, not to paper over.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/multi_segment_static_data_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("multi_segment_static_data.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Every export and the number of i32 args it takes (all take none here).
EXPORTS = [
    "a_lo", "a_hi", "b_straddle", "b_after", "c_head", "c_ovl",
    "d_lo", "d_hi", "d_byte", "e_0", "e_16", "e_28", "gap",
]

PAGE = 0x10000


def wasmtime_truth():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return {fn: inst.exports(store)[fn](store) & 0xFFFFFFFF for fn in EXPORTS}


def compile_synth(out, extra):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "--all-exports",
           "-b", "arm", "--target", "cortex-m3"] + extra
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed ({' '.join(extra) or 'self-contained'}): {r.stderr}")


def load_syms(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    return f, text.data(), text["sh_addr"], syms


# --- The wasm init image the embedder would map into memory 0 (relocatable
# path). Built here from the SAME segments as the .wat so the relocatable side
# checks addressing against a known-good memory, not against synth's own copy. ---
def wasm_init_image(size):
    img = bytearray(size)
    for off, data in (
        (0x40, b"\x11\x22\x33\x44\x55\x66\x77\x88"),
        (0x0FFE, b"\xa1\xb2\xc3\xd4\xe5\xf6\x07\x18"),
        (0x200, b"\xde\xad\xbe\xef"),
        (0x203, b"\x99\xaa"),
        (0x1FF0, b"\xca\xfe\xba\xbe\x0d\xf0\xad\x8b"),
        (0x800, bytes(range(1, 0x21))),
    ):
        img[off:off + len(data)] = data
    return bytes(img)


# ---------------------------------------------------------------------------
# Self-contained image: zeroed RAM, real reset path (ROM->RAM copy).
# ---------------------------------------------------------------------------
FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
RET = 0x000F_0000


class SelfContainedRunner:
    def __init__(self, code, base, syms):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(FLASH, 0x100000)
        self.mu.mem_map(RAM, RAM_SIZE)  # zeroed RAM: inits must come from startup
        self.mu.mem_map(0xE000E000, 0x1000)  # SCS page
        self.mu.mem_write(base, code)
        self.sp = int.from_bytes(code[0:4], "little")
        reset = syms.get("Reset_Handler")
        if reset is None:
            sys.exit("Reset_Handler missing from symtab")
        stop = code.find(b"\x01\x48\x80\x47", (reset & ~1) - base)
        if stop < 0:
            sys.exit("startup call scaffold (LDR r0/BLX r0) not found")
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.emu_start(reset | 1, base + stop, count=200000)

    def call(self, fn):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            self.mu.emu_start(faddr | 1, RET, count=200000)
        except UcError as e:
            return f"ERR:{e}"
        return self.mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


# ---------------------------------------------------------------------------
# Relocatable object: memory 0 at the runtime R11 base, embedder-populated init.
# .text mapped FAR from the memory base so a baked-absolute offset faults.
# ---------------------------------------------------------------------------
REL_TEXT = 0x0010_0000
REL_MEM0 = 0x4000_0000  # R11 base — 2 wasm pages
REL_STACK = 0x6000_0000


class RelocatableRunner:
    def __init__(self, code, base, syms):
        self.syms = syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(REL_TEXT, 0x10000)
        self.mu.mem_map(REL_MEM0, 2 * PAGE)
        self.mu.mem_map(REL_STACK, PAGE)
        self.mu.mem_write(REL_TEXT, code)
        self.ret = REL_TEXT + 0x10000 - 0x10
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")
        self.init = wasm_init_image(2 * PAGE)

    def call(self, fn):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
        # Fresh wasm instance: re-seed memory 0 from the embedder's init image.
        self.mu.mem_write(REL_MEM0, self.init)
        self.mu.reg_write(UC_ARM_REG_R10, 2 * PAGE)  # memory 0 size in bytes
        self.mu.reg_write(UC_ARM_REG_R11, REL_MEM0)  # memory 0 base
        self.mu.reg_write(UC_ARM_REG_SP, REL_STACK + PAGE - 0x100)
        self.mu.reg_write(UC_ARM_REG_LR, self.ret | 1)
        entry = REL_TEXT + (faddr & ~1)
        try:
            self.mu.emu_start(entry | 1, self.ret, count=200000)
        except UcError as e:
            return f"ERR:{e}"
        return self.mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def run_path(label, runner, truth):
    print(f"=== {label} ===")
    fails = 0
    for fn in EXPORTS:
        exp = truth[fn]
        got = runner.call(fn)
        ok = isinstance(got, int) and got == exp
        if not ok:
            fails += 1
        shown = hex(got) if isinstance(got, int) else got
        print(f"  [{'ok ' if ok else 'BUG'}] {fn}() -> {shown}  (wasmtime {exp:#x})")
    return fails


def main():
    truth = wasmtime_truth()
    tmp = Path(tempfile.mkdtemp(prefix="mss_"))

    sc_elf = str(tmp / "sc.elf")
    compile_synth(sc_elf, [])
    _, code, base, syms = load_syms(sc_elf)
    sc_fails = run_path(
        "self-contained --cortex-m (zeroed RAM, real reset ROM->RAM copy)",
        SelfContainedRunner(code, base, syms), truth)

    rel_o = str(tmp / "rel.o")
    compile_synth(rel_o, ["--relocatable"])
    _, code, base, syms = load_syms(rel_o)
    rel_fails = run_path(
        "relocatable (memory 0 at R11, embedder-populated init, .text far away)",
        RelocatableRunner(code, base, syms), truth)

    total = sc_fails + rel_fails
    print(f"\nORACLE: {'PASS' if total == 0 else f'FAIL ({total} divergences)'}")
    sys.exit(0 if total == 0 else 1)


if __name__ == "__main__":
    main()
