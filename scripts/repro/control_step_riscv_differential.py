#!/usr/bin/env python3
"""#223 / #798 — control_step on RISC-V: correctness + ABI + shipped-data differential.

After #218 (reachable) + #220 (callee-saved ABI) + #223 (Select, non-param
locals, sign-extend), gale's `control_step_decide` compiles to RV32. This checks
it computes the SAME result as wasmtime (and the ARM backend — gale's reference
`(3000,50,40,0) = 0x00210a55`), reads its `.rodata` table via s11 (the linmem
base), and preserves the caller's callee-saved registers.

DE-VACUATED for #798: linear memory is initialized from the object's SHIPPED
`.wasm_data` active-segment records (the exact bytes the generated startup's
record-copy loop places at `s11 + off`), NOT from wasmtime's instantiated
memory. The old harness copied wasmtime's memory image into unicorn, which
masked the silent initializer drop the VCR-VER-003 phase-2 probe found — the
object shipped `.text` only, every load of the 1200-byte decision table read
0x00, and this differential stayed green anyway (a VACUOUS gate). Now:

  - an object WITHOUT `.wasm_data` fails LOUDLY up front (the drop is visible);
  - the emulated linmem holds exactly what the shipped records serve, so a
    packing/offset bug diverges from wasmtime here.

Record format (see synth_core::static_data_addr::pack_segment_records):
repeated [u32 LE linmem_off][u32 LE len][len bytes][pad to 4], declaration
order — the startup copies them in record order, so later-wins is preserved.

Run:
  synth compile scripts/repro/control_step.wasm -b riscv -t rv32imac \
        --all-exports --relocatable -o /tmp/cs_rv.o
  /tmp/armv/bin/python scripts/repro/control_step_riscv_differential.py /tmp/cs_rv.o
"""
import struct
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_A2,
    UC_RISCV_REG_A3,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S1,
    UC_RISCV_REG_S2,
    UC_RISCV_REG_S7,
    UC_RISCV_REG_S8,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WASM = "scripts/repro/control_step.wasm"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/cs_rv.o"
SYNTH = "./target/debug/synth"
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000
SENTINELS = {
    UC_RISCV_REG_S1: 0x1111_1111,
    UC_RISCV_REG_S2: 0x2222_2222,
    UC_RISCV_REG_S7: 0x7777_7777,  # non-param locals land in s7/s8 region
    UC_RISCV_REG_S8: 0x8888_8888,
}
VECTORS = [(3000, 50, 40, 0), (0, 0, 0, 0), (1500, 0, 0, 0), (2645, 10, 20, 0), (4000, 200, 30, 7)]


def shipped_records(elffile):
    """Parse the shipped `.wasm_data` active-segment records (#798).

    Returns a declaration-order list of (linmem_off, bytes), or None when the
    object ships no `.wasm_data` section at all (the pre-#798 silent drop).
    """
    sec = elffile.get_section_by_name(".wasm_data")
    if sec is None:
        return None
    blob = sec.data()
    recs, i = [], 0
    while i + 8 <= len(blob):
        off, ln = struct.unpack_from("<II", blob, i)
        i += 8
        assert i + ln <= len(blob), f"truncated .wasm_data record at {i}"
        recs.append((off, blob[i:i + ln]))
        i = (i + ln + 3) & ~3
    assert i == len(blob), f".wasm_data has {len(blob) - i} trailing bytes"
    return recs


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())

    def wt(args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)["control_step_decide"](store, *args) & 0xFFFFFFFF

    # Read the function offset from the ELF SYMBOL TABLE (host-independent), NOT
    # by parsing `synth disasm` TEXT — disasm formatting is host-dependent and the
    # regex matched nothing on the Linux CI runner (#850). In a --relocatable RV32
    # object a function symbol's st_value IS its offset within .text (base 0, no
    # Thumb bit), exactly the `fa` unicorn expects at CODE + fa.
    elffile = ELFFile(open(ELF, "rb"))
    text_idx = elffile.get_section_index(".text")
    syms = {s.name: s["st_value"] for sec in elffile.iter_sections()
            if sec.header.sh_type == "SHT_SYMTAB"
            for s in sec.iter_symbols()
            if s.name and s["st_shndx"] == text_idx}
    fa = syms["func_0"] if "func_0" in syms else syms.get("control_step_decide")
    if fa is None:
        print(f"FAIL: control_step_decide symbol not found ({sorted(syms)})")
        sys.exit(1)
    code = elffile.get_section_by_name(".text").data()

    # #798 gate: the module carries a nonzero active data segment (the decision
    # table at linmem 0x10000); an object that ships no .wasm_data records
    # drops it silently — every table load reads 0x00. Fail LOUDLY up front.
    recs = shipped_records(elffile)
    if recs is None:
        print("RISC-V control_step ORACLE: FAIL — object ships NO .wasm_data "
              "records; the active data segment (decision table @ 0x10000) is "
              "silently dropped (#798), linmem reads return 0x00")
        sys.exit(1)
    total = sum(len(b) for _, b in recs)
    print(f"shipped .wasm_data: {len(recs)} record(s), {total} initializer byte(s)")

    def run(args):
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        mu.mem_map(CODE, 0x20000)
        mu.mem_map(LIN, 0x20000)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        # Linear memory init = the SHIPPED records, applied in record order
        # (later-wins) — exactly what the generated startup copy loop does.
        for off, b in recs:
            mu.mem_write(LIN + off, bytes(b))
        mu.reg_write(UC_RISCV_REG_SP, STK)
        mu.reg_write(UC_RISCV_REG_S11, LIN)  # s11 = __linear_memory_base
        for r, v in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_A2, UC_RISCV_REG_A3), args):
            mu.reg_write(r, v & 0xFFFFFFFF)
        for r, v in SENTINELS.items():
            mu.reg_write(r, v)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + fa, RET, count=2000)
        except UcError as e:
            return None, False, str(e)
        res = mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
        preserved = all((mu.reg_read(r) & 0xFFFFFFFF) == v for r, v in SENTINELS.items())
        return res, preserved, ""

    fails = 0
    for v in VECTORS:
        gt = wt(v)
        res, preserved, err = run(v)
        ok = res == gt and preserved
        fails += 0 if ok else 1
        shown = f"0x{res:08x}" if res is not None else f"ERR({err})"
        print(f"control_step{v} = {shown}  wasmtime=0x{gt:08x}  s-regs-preserved={preserved}"
              f"  {'OK' if ok else 'FAIL'}")
    print("\nRISC-V control_step ORACLE: PASS (correct + ABI-compliant + data shipped)"
          if not fails else f"RISC-V control_step ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
