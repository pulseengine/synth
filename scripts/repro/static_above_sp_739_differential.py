#!/usr/bin/env python3
"""#739 execution differential: static ABOVE sp_init under --shadow-stack-size.

A meld `--memory shared` fused node places component statics ABOVE the shared
SP (17-page linmem, SP init 0x100000, statics at 0x10000C / 0x100020). Pre-fix
the sub-word load/store lowering BAKED those static-region memarg offsets as
plain un-relocated `MOVW/MOVT ip` immediates (`movw ip,#0xC; movt ip,#0x10`),
so:
  * the #678 `--shadow-stack-size` rebase (which walks RELOCATIONS) never
    re-based them -> OOB access on the shrunk reservation (read zeros /
    unmapped) — gale's gust:os zeroed log buffer;
  * the post-link "all reservation accesses in-range" oracle (also
    reloc-walking) passed anyway — a vacuous gate (the #712-class lesson).

This oracle runs the compiled object (unicorn Thumb-2, R11 = 0 native deref,
`.bss`/`.data` at SEPARATE bases so a baked absolute linmem offset cannot
accidentally work) against wasmtime ground truth on the same wat:

  run(p)       — store (43+2p) as a byte through the DYNAMIC-index +
                 static-offset shape at [0x10000C + p], read it back.
                 RED pre-fix: the baked access faults / reads zero.
  peek_data(i) — byte read from the initialized `(data)` segment ABOVE
                 sp_init at [0x100020 + i] (retargeted to __synth_wasm_seg_0).

Also pins that the shrink actually FIRED (the `.bss` reservation is the
shrunk budget-sized one, not the 1 MiB page) and that every relocated
static falls inside it — the in-range property the old oracle only claimed.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/static_above_sp_739_differential.py
Exits nonzero on any mismatch.
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
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("mem739_above_sp.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
ABS32 = 2
BUDGET = 2048
SP_INIT = 0x100000

# Distinct bases per linker-placed region — the point: a BAKED absolute wasm
# linmem offset (0x10000C) lands in none of them, while a properly relocated
# `__synth_wasm_data + C'` resolves into the shrunk `.bss`.
BASES = {".text": 0x10000, ".bss": 0x40000, ".data": 0x60000}
MAPSZ = 0x10000


def wasmtime_truth(fn, arg):
    """Fresh instance per call (store-then-load must not leak across cases)."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, arg) & 0xFFFFFFFF


def main():
    obj = Path(tempfile.mkdtemp(prefix="mem739_")) / "mem739.o"
    subprocess.run(
        [
            SYNTH,
            "compile",
            str(WAT),
            "-o",
            str(obj),
            "--target",
            "cortex-m3",
            "--native-pointer-abi",
            "--all-exports",
            "--relocatable",
            "--shadow-stack-size",
            str(BUDGET),
        ],
        check=True,
        capture_output=True,
    )

    e = ELFFile(open(obj, "rb"))
    secname_by_idx = {i: s.name for i, s in enumerate(e.iter_sections())}
    text = bytearray(e.get_section_by_name(".text").data())
    bss = e.get_section_by_name(".bss")
    data_sec = e.get_section_by_name(".data")
    if bss is None or data_sec is None:
        print("FAIL: object lacks .bss/.data — the native-pointer region was dropped")
        return 1
    data = bytearray(data_sec.data())
    bss_size = bss["sh_size"]

    # The shrink must have FIRED: reservation ~= budget + above-SP tail,
    # nowhere near the 1 MiB page. Pre-fix the compile either drops the
    # region entirely (no relocs at all) or reserves the full extent.
    if not (BUDGET <= bss_size <= BUDGET + 4096):
        print(f"FAIL: .bss is {bss_size} B — shrink did not fire (budget {BUDGET})")
        return 1

    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {}
    for s in symtab.iter_symbols():
        syms[s.name] = (s["st_shndx"], s["st_value"])

    # Relocate every R_ARM_ABS32 literal-pool word in place: final address =
    # base(section owning the symbol) + symbol value + in-place addend (REL).
    # In-range pin: a reloc into `.bss` must target the SHRUNK reservation —
    # the property the pre-fix oracle claimed without seeing baked offsets.
    for r in e.get_section_by_name(".rel.text").iter_relocations():
        if r["r_info_type"] != ABS32:
            continue
        sym = symtab.get_symbol(r["r_info_sym"])
        shndx, val = syms[sym.name]
        secname = secname_by_idx[shndx]
        (add,) = struct.unpack_from("<I", text, r["r_offset"])
        if secname == ".bss" and val + add + 1 > bss_size:
            print(
                f"FAIL: reloc {sym.name}+{add:#x} targets past the shrunk "
                f".bss ({bss_size} B) — un-rebased static (#739)"
            )
            return 1
        struct.pack_into(
            "<I", text, r["r_offset"], (BASES[secname] + val + add) & 0xFFFFFFFF
        )

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    for _, base in BASES.items():
        mu.mem_map(base, MAPSZ)
    mu.mem_write(BASES[".text"], bytes(text))
    mu.mem_write(BASES[".data"], bytes(data))
    RET = BASES[".text"] + 0xFF0
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")

    def run_arm(fn, arg):
        # Re-zero .bss between runs (fresh wasm instance semantics).
        mu.mem_write(BASES[".bss"], b"\x00" * bss_size)
        mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R11, 0)  # native deref: fp/base = 0
        mu.reg_write(UC_ARM_REG_SP, BASES[".bss"] + MAPSZ - 0x100)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        entry = BASES[".text"] + (syms[fn][1] & ~1)
        mu.emu_start(entry | 1, RET, timeout=5_000_000)
        return mu.reg_read(UC_ARM_REG_R0)

    ok = True
    cases = [("run", p) for p in (0, 1, 5, 7)] + [("peek_data", i) for i in range(4)]
    for fn, arg in cases:
        exp = wasmtime_truth(fn, arg)
        try:
            got = run_arm(fn, arg)
        except UcError as ex:
            print(f"{fn}({arg}) = UNICORN FAULT {ex} (expect {exp})")
            ok = False
            continue
        match = "" if got == exp else "  <-- MISMATCH"
        print(f"{fn}({arg}) = {got} (expect {exp}){match}")
        ok &= got == exp

    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
