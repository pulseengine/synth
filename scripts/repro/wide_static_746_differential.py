#!/usr/bin/env python3
"""#746 execution differential: i64/wide static ABOVE sp_init under
--shadow-stack-size (the #739 residual — sub-word arms were fixed in #744).

A meld `--memory shared` fused node places component statics ABOVE the shared
SP (17-page linmem, SP init 0x100000, statics at 0x100010 / 0x100020). #744
relocated the i32 sub-word static-region arms; the WIDE (i64) and i64 NARROW
(load8/16/32, store8/16/32) arms still LOUD-DECLINED:

    #739: i64.load with static-region memarg offset 1048584 (>= wasm_data_base
    1048576) under the native-pointer ABI is not yet relocated — declining

so any function bulk-copying a static via i64 (gale's gust:os `log.line`
message emit) was skipped and the object unlinkable. RED pre-#746: this
script's compile step fails ("no functions compiled successfully"). GREEN
post-#746: every arm relocates its base to `__synth_wasm_data + offset`
(reloc-visible to the #678 shrink rebase) + the dynamic index, and execution
matches wasmtime.

This oracle runs the compiled object (unicorn Thumb-2, R11 = 0 native deref,
`.bss`/`.data` at SEPARATE bases so a baked absolute linmem offset cannot
accidentally work) against wasmtime ground truth on the same wat:

  run64lo/run64hi(p) — i64 store + load through the dynamic-index +
                       static-offset shape at [0x100010 + p], both halves.
  narrow32/16s/8(p)  — i64.store32/16/8 + i64.load32_u/16_s/8_u round-trips
                       through the BSS static at [0x100018 + p].
  peek_data8/16s(i)  — i64 narrow reads from the initialized `(data)` segment
                       ABOVE sp_init (retargeted to __synth_wasm_seg_0).

Also pins that the shrink actually FIRED (the `.bss` reservation is the
shrunk budget-sized one, not the 1 MiB page) and that every relocated static
falls inside it.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/wide_static_746_differential.py
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

WAT = Path(__file__).with_name("mem746_wide_static.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
ABS32 = 2
BUDGET = 2048
SP_INIT = 0x100000

# Distinct bases per linker-placed region — the point: a BAKED absolute wasm
# linmem offset (0x100010) lands in none of them, while a properly relocated
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
    obj = Path(tempfile.mkdtemp(prefix="mem746_")) / "mem746.o"
    proc = subprocess.run(
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
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        # RED pre-#746: the i64/wide arms decline and every function is
        # skipped -> "no functions compiled successfully".
        print(proc.stderr.strip())
        print("FAIL: compile declined — the i64/wide static-region arms are")
        print("      not relocated (#746 residual of #739)")
        return 1

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
    # nowhere near the 1 MiB page.
    if not (BUDGET <= bss_size <= BUDGET + 4096):
        print(f"FAIL: .bss is {bss_size} B — shrink did not fire (budget {BUDGET})")
        return 1

    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {}
    for s in symtab.iter_symbols():
        syms[s.name] = (s["st_shndx"], s["st_value"])

    # Relocate every R_ARM_ABS32 literal-pool word in place: final address =
    # base(section owning the symbol) + symbol value + in-place addend (REL).
    # In-range pin: a reloc into `.bss` must target the SHRUNK reservation
    # (the hi half of each i64 pair access, [base, #4], is exercised by the
    # run64hi execution cases below).
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
                f".bss ({bss_size} B) — un-rebased static (#746)"
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
    cases = (
        [("run64lo", p) for p in (0, 4, 8)]
        + [("run64hi", p) for p in (0, 4, 8)]
        + [("narrow32", p) for p in (0, 4)]
        + [("narrow16s", p) for p in (0, 2)]
        + [("narrow8", p) for p in (0, 1, 3)]
        + [("peek_data8", i) for i in range(8)]
        + [("peek_data16s", i) for i in (0, 2, 4, 6)]
    )
    for fn, arg in cases:
        exp = wasmtime_truth(fn, arg)
        try:
            got = run_arm(fn, arg)
        except UcError as ex:
            print(f"{fn}({arg}) = UNICORN FAULT {ex} (expect {exp})")
            ok = False
            continue
        match = "" if got == exp else "  <-- MISMATCH"
        print(f"{fn}({arg}) = {got:#x} (expect {exp:#x}){match}")
        ok &= got == exp

    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
