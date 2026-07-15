#!/usr/bin/env python3
"""#406 (VCR-MEM-002 phase 1) execution differential: two wasm linear
memories must be two DISTINCT native regions.

Pre-#406 the decoder dropped the memarg memory index, so every load/store
lowered onto the ONE R11 base — a store to memory 1 silently clobbered
memory 0 (`store_both_read0` returned y instead of x), memory 1's init data
was silently dropped, and `memory.size` on memory 1 read memory 0's R10.

Post-#406 (`--relocatable`): memory 0 keeps the runtime R11 base (byte-
identical to the single-memory lowering); memory 1 is addressed through its
own `__synth_wasm_data_1` symbol (R_ARM_ABS32 literal-pool words) defined at
the base of the object's `.synth.wasm_mem_1` reservation section.

This oracle compiles `mem406_multi_memory.wat` with `--relocatable`, maps the
two memories at DISTINCT unicorn bases (memory 0 at the R11 base, memory 1 at
the address the ABS32 relocs are patched to — deliberately far apart so any
residual aliasing faults or mismatches), and checks every export against
wasmtime multi-memory ground truth. Also pins the structure: the object must
DEFINE `__synth_wasm_data_1`, carry a `.synth.wasm_mem_1` PROGBITS section of
exactly 3 wasm pages with the init segment placed at offset 16, and every
ABS32 reloc against it must land in-range.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/multi_memory_406_differential.py
Exits nonzero on any mismatch. RED pre-#406 (silent aliasing / dropped init
data), GREEN post-#406.
"""

import os
import struct
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
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("mem406_multi_memory.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
ABS32 = 2
PAGE = 0x10000

# Distinct bases per region — the point of the whole exercise. Memory 0 lives
# at the R11 base; memory 1 lives where the `__synth_wasm_data_1` relocs are
# patched to. Far apart: a store aliased onto the wrong base lands in the
# other region (value mismatch) or unmapped space (unicorn fault) — never
# accidentally correct.
TEXT_BASE = 0x10000
MEM0_BASE = 0x200000  # R11 (1 wasm page)
MEM1_BASE = 0x400000  # __synth_wasm_data_1 (3 wasm pages)
STACK_BASE = 0x600000
MEM1_SECTION = ".synth.wasm_mem_1"


def wasmtime_truth(fn, args):
    """Fresh instance per call (store-then-load must not leak across cases)."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, *args) & 0xFFFFFFFF


def main():
    obj = Path(tempfile.mkdtemp(prefix="mem406_")) / "mem406.o"
    proc = subprocess.run(
        [
            SYNTH,
            "compile",
            str(WAT),
            "-o",
            str(obj),
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
        ],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        print(proc.stderr.strip())
        print("FAIL: compile declined — multi-memory not lowered (#406)")
        return 1

    e = ELFFile(open(obj, "rb"))
    secname_by_idx = {i: s.name for i, s in enumerate(e.iter_sections())}
    text = bytearray(e.get_section_by_name(".text").data())

    # Structural pins: the per-memory region + its base symbol.
    mem1 = e.get_section_by_name(MEM1_SECTION)
    if mem1 is None:
        print(f"FAIL: object lacks {MEM1_SECTION} — memory 1 has no region (#406)")
        return 1
    if mem1["sh_size"] != 3 * PAGE:
        print(f"FAIL: {MEM1_SECTION} is {mem1['sh_size']} B, want {3 * PAGE} (3 pages)")
        return 1
    if mem1["sh_type"] != "SHT_PROGBITS":
        print(f"FAIL: {MEM1_SECTION} is {mem1['sh_type']} — init segment dropped (#406)")
        return 1
    mem1_image = bytes(mem1.data())
    if mem1_image[16:24] != b"\xaa\xbb\xcc\xdd\x11\x22\x33\x44":
        print("FAIL: memory 1's init segment bytes not placed at offset 16 (#406)")
        return 1

    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {}
    for s in symtab.iter_symbols():
        syms[s.name] = (s["st_shndx"], s["st_value"])
    if "__synth_wasm_data_1" not in syms or not isinstance(
        syms["__synth_wasm_data_1"][0], int
    ):
        print("FAIL: __synth_wasm_data_1 is not a DEFINED symbol (#406)")
        return 1

    # Patch every ABS32 literal-pool word: memory 1's words to MEM1_BASE (with
    # an in-range pin), anything else to its own section base (none expected on
    # this plain-relocatable fixture, but stay general).
    sec_bases = {MEM1_SECTION: MEM1_BASE, ".text": TEXT_BASE}
    rel = e.get_section_by_name(".rel.text")
    n_mem1_relocs = 0
    for r in rel.iter_relocations() if rel is not None else []:
        if r["r_info_type"] != ABS32:
            continue
        sym = symtab.get_symbol(r["r_info_sym"])
        shndx, val = syms[sym.name]
        secname = secname_by_idx[shndx]
        (add,) = struct.unpack_from("<I", text, r["r_offset"])
        if secname == MEM1_SECTION:
            n_mem1_relocs += 1
            if val + add + 1 > 3 * PAGE:
                print(
                    f"FAIL: reloc {sym.name}+{add:#x} targets past memory 1's "
                    f"3-page region (#406)"
                )
                return 1
        if secname not in sec_bases:
            print(f"FAIL: unexpected ABS32 reloc into section {secname}")
            return 1
        struct.pack_into(
            "<I", text, r["r_offset"], (sec_bases[secname] + val + add) & 0xFFFFFFFF
        )
    if n_mem1_relocs == 0:
        print("FAIL: no ABS32 reloc against __synth_wasm_data_1 — memory 1 ops")
        print("      are not symbol-addressed (silent aliasing, pre-#406)")
        return 1

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(TEXT_BASE, PAGE)
    mu.mem_map(MEM0_BASE, PAGE)  # memory 0: 1 wasm page
    mu.mem_map(MEM1_BASE, 3 * PAGE)  # memory 1: 3 wasm pages
    mu.mem_map(STACK_BASE, PAGE)
    mu.mem_write(TEXT_BASE, bytes(text))
    RET = TEXT_BASE + PAGE - 0x10
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")

    def run_arm(fn, args):
        # Fresh wasm instance semantics: re-zero memory 0, re-init memory 1
        # from its section image (the embedder's mapping contract).
        mu.mem_write(MEM0_BASE, b"\x00" * PAGE)
        mu.mem_write(MEM1_BASE, mem1_image)
        for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2), args):
            mu.reg_write(reg, val & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R10, PAGE)  # memory 0's size in bytes (1 page)
        mu.reg_write(UC_ARM_REG_R11, MEM0_BASE)  # memory 0's base
        mu.reg_write(UC_ARM_REG_SP, STACK_BASE + PAGE - 0x100)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        entry = TEXT_BASE + (syms[fn][1] & ~1)
        mu.emu_start(entry | 1, RET, timeout=5_000_000)
        return mu.reg_read(UC_ARM_REG_R0)

    X, Y = 0x11111111, 0x22222222
    cases = (
        # The aliasing discriminators: distinct values, same in-memory offset.
        [("store_both_read0", (p, X, Y)) for p in (0, 4, 64)]
        + [("store_both_read1", (p, X, Y)) for p in (0, 4, 64)]
        # Init-data peeks (pre-#406: segment dropped, would read 0).
        + [("peek1_8u", (i,)) for i in range(8)]
        + [("peek1_16u", (i,)) for i in (0, 2, 4, 6)]
        + [("peek1_32", (i,)) for i in (0, 4)]
        # Sub-word round-trips on memory 1 (sign/zero extends).
        + [("narrow1_8", (p, v)) for p, v in ((0, 0x7F), (1, 0x80), (3, 0xFF))]
        + [("narrow1_16", (p, v)) for p, v in ((0, 0x7FFF), (2, 0x8000))]
        # Per-memory size/grow: sizes DIFFER (1 vs 3), grow fails both sides.
        + [("size0", ()), ("size1", ()), ("grow1", (1,)), ("grow1", (5,))]
    )
    ok = True
    for fn, args in cases:
        exp = wasmtime_truth(fn, args)
        try:
            got = run_arm(fn, args)
        except UcError as ex:
            print(f"{fn}{args} = UNICORN FAULT {ex} (expect {exp:#x})")
            ok = False
            continue
        match = "" if got == exp else "  <-- MISMATCH"
        print(f"{fn}{args} = {got:#x} (expect {exp:#x}){match}")
        ok &= got == exp

    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
