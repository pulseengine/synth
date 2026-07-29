#!/usr/bin/env python3
"""#871 — RV32 external-call relocations: read-back + link + execution oracle.

gale's thin-seam drivers import a two-function mmio seam (env::mmio_read32 /
env::mmio_write32). Pre-fix, `-b riscv --relocatable` SKIPPED every
seam-using export ("external call without relocation table") — no driver
could dissolve to RISC-V while the identical wasm lowered fine to cortex-m3.
The fix mirrors the ARM contract: an external `call` emits the canonical
8-byte `auipc ra, 0 ; jalr ra, 0(ra)` placeholder plus an `R_RISCV_CALL_PLT`
relocation against the import's field name (an UNDEFINED symbol the host
linker resolves).

What this harness proves (each numbered stage hard-fails on violation):
  1. COMPLETENESS — every export of the gale-shaped fixture emits as a
     defined `T` symbol and `nm -u` lists exactly the imports (the 2-fn
     mmio seam + a void barrier — the common driver seam shape). Pre-fix:
     only the import-free exports emitted, no undefined symbols (RED).
  2. RELOC READ-BACK — every `.rela.text` entry has type R_RISCV_CALL_PLT
     (19), a 4-aligned r_offset inside `.text`, resolves to the right
     import symbol, and the bytes at r_offset are the exact placeholder
     pair (a reloc at the wrong offset/symbol is a silent link-time
     miscompile). Per-function site counts are checked (see EXPORTS).
  3. ARM PARITY — the SAME wasm compiled `--target cortex-m3 --relocatable`
     has the same defined-export set and the same undefined-import set.
  4. REAL LINK (when ld.lld + clang with RV32 support are on PATH) — the
     object links against a 3-stub mmio implementation with ZERO undefined
     symbols, and the patched call sites are verified to land on the stubs.
  5. EXECUTION — the LINKED image runs under unicorn (UC_ARCH_RISCV /
     RV32) against wasmtime ground truth (imports modelled as a Python
     mmio register file) for every (export, input): return values AND the
     final mmio memory contents must be bit-identical.

Run (needs wasmtime + unicorn + pyelftools):
  /tmp/ci_env/bin/python scripts/repro/riscv_extern_call_871_differential.py
Env: SYNTH=path-to-synth (default ./target/release/synth).
Exits nonzero on any mismatch.
"""

import os
import shutil
import struct
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_PC,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/riscv_extern_call_871.wat"
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

R_RISCV_CALL_PLT = 19
CALL_PLACEHOLDER = bytes([0x97, 0x00, 0x00, 0x00, 0xE7, 0x80, 0x00, 0x00])

IMPORTS = {"mmio_read32", "mmio_write32", "mmio_barrier"}
EXPORTS = {
    # name -> expected number of R_RISCV_CALL_PLT sites
    "wdg_status": 1,
    "wdg_kick": 1,
    "wdg_set_bit": 2,
    "wdg_sum2": 2,
    "wdg_flush": 1,
    "wdg_is_running": 0,
    "wdg_lock": 0,
}

# Execution cases: mmio addresses live in the dedicated MMIO page.
MMIO_BASE = 0x30000000
CASES = {
    "wdg_status": [(MMIO_BASE,), (MMIO_BASE + 8,)],
    "wdg_kick": [(MMIO_BASE,), (MMIO_BASE + 0x10,)],
    "wdg_set_bit": [(MMIO_BASE, 1), (MMIO_BASE + 4, 0x80000000), (MMIO_BASE + 8, 0)],
    "wdg_sum2": [(MMIO_BASE, MMIO_BASE + 4), (MMIO_BASE + 8, MMIO_BASE + 8)],
    "wdg_flush": [(7,), (0x40000000,)],
    "wdg_is_running": [(0,), (1,), (0xFFFFFFFE,)],
    "wdg_lock": [(1,), (0x20000001,)],
}
# Initial mmio register file contents (word offset -> value), same both sides.
MMIO_INIT = {0x0: 0xDEADBEEF, 0x4: 0x00000001, 0x8: 0x40000000, 0x10: 0x12345678}
MMIO_SIZE = 0x1000

CODE, STK, RET = 0x100000, 0x90000, 0x200000


def die(msg):
    sys.exit(f"FAIL: {msg}")


def compile_obj(out, extra):
    r = subprocess.run(
        [SYNTH, "compile", WAT, "-o", out, "--all-exports", "--relocatable"] + extra,
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        die(f"compile {extra} failed: {r.stderr}")
    return r.stderr


def read_symbols(path):
    """Return (defined {name: (value, size)}, undefined {name})."""
    defined, undefined = {}, set()
    with open(path, "rb") as f:
        elf = ELFFile(f)
        for sec in elf.iter_sections():
            if sec["sh_type"] != "SHT_SYMTAB":
                continue
            for sym in sec.iter_symbols():
                if not sym.name:
                    continue
                if sym["st_shndx"] == "SHN_UNDEF":
                    undefined.add(sym.name)
                else:
                    defined[sym.name] = (sym["st_value"], sym["st_size"])
    return defined, undefined


def stage1_completeness(obj):
    defined, undefined = read_symbols(obj)
    missing = set(EXPORTS) - set(defined)
    if missing:
        die(f"stage1: exports missing from RV32 object (the #871 RED shape): {sorted(missing)}")
    if undefined != IMPORTS:
        die(f"stage1: undefined symbols {sorted(undefined)} != expected {sorted(IMPORTS)}")
    print(f"stage1 OK: {len(EXPORTS)} exports defined (T), nm -u == {sorted(IMPORTS)}")
    return defined


def stage2_reloc_readback(obj, defined):
    with open(obj, "rb") as f:
        elf = ELFFile(f)
        text = elf.get_section_by_name(".text")
        text_bytes = text.data()
        rela = elf.get_section_by_name(".rela.text")
        if rela is None:
            die("stage2: no .rela.text section in the RV32 object")
        symtab = elf.get_section(rela["sh_link"])
        per_func = dict.fromkeys(EXPORTS, 0)
        for rel in rela.iter_relocations():
            rtype = rel["r_info_type"]
            roff = rel["r_offset"]
            rsym = symtab.get_symbol(rel["r_info_sym"]).name
            if rtype != R_RISCV_CALL_PLT:
                die(f"stage2: reloc at {roff:#x} has type {rtype}, want R_RISCV_CALL_PLT (19)")
            if rel["r_addend"] != 0:
                die(f"stage2: reloc at {roff:#x} has addend {rel['r_addend']}, want 0")
            if roff % 4 != 0 or roff + 8 > len(text_bytes):
                die(f"stage2: reloc offset {roff:#x} misaligned or out of .text")
            if rsym not in IMPORTS:
                die(f"stage2: reloc at {roff:#x} targets '{rsym}', not an import")
            got = text_bytes[roff : roff + 8]
            if got != CALL_PLACEHOLDER:
                die(
                    f"stage2: bytes at reloc site {roff:#x} are {got.hex()} — "
                    f"expected the auipc/jalr placeholder {CALL_PLACEHOLDER.hex()}"
                )
            # attribute the site to its containing function
            owner = None
            for name, (val, size) in defined.items():
                if name in EXPORTS and val <= roff < val + size:
                    owner = name
            if owner is None:
                die(f"stage2: reloc at {roff:#x} is outside every export's [value, value+size)")
            per_func[owner] += 1
        if per_func != EXPORTS:
            die(f"stage2: per-function call-site counts {per_func} != expected {EXPORTS}")
    total = sum(EXPORTS.values())
    print(f"stage2 OK: {total} R_RISCV_CALL_PLT relocs, correct offsets/symbols/placeholder bytes")


def stage3_arm_parity(arm_obj):
    defined, undefined = read_symbols(arm_obj)
    arm_exports = {n for n in defined if n in EXPORTS}
    if arm_exports != set(EXPORTS):
        die(f"stage3: ARM object exports {sorted(arm_exports)} != {sorted(EXPORTS)}")
    arm_undef = {n for n in undefined if not n.startswith("__")}
    if arm_undef != IMPORTS:
        die(f"stage3: ARM undefined imports {sorted(arm_undef)} != {sorted(IMPORTS)}")
    print("stage3 OK: RV32 object matches the ARM export/undefined-symbol shape")


def find_rv32_linker():
    """Return (clang, lld) paths when both can target rv32, else None.

    Apple clang has no RISC-V backend, so prefer a Homebrew/PATH LLVM clang
    and PROBE each candidate by assembling a nop for riscv32.
    """
    clangs = [
        "/opt/homebrew/opt/llvm/bin/clang",
        "/usr/local/opt/llvm/bin/clang",
        shutil.which("clang"),
    ]
    llds = [
        shutil.which("ld.lld"),
        "/opt/homebrew/opt/llvm/bin/ld.lld",
        "/usr/local/opt/llvm/bin/ld.lld",
    ]
    lld = next((c for c in llds if c and os.path.exists(c)), None)
    if lld is None:
        return None
    for clang in clangs:
        if not clang or not os.path.exists(clang):
            continue
        probe = subprocess.run(
            [clang, "--target=riscv32-unknown-elf", "-march=rv32imac", "-x", "assembler",
             "-c", "-", "-o", os.devnull],
            input="nop\n", capture_output=True, text=True,
        )
        if probe.returncode == 0:
            return clang, lld
    return None


STUB_ASM = """
    .text
    .globl mmio_read32
mmio_read32:
    lw a0, 0(a0)
    ret
    .globl mmio_write32
mmio_write32:
    sw a1, 0(a0)
    mv a0, a1
    ret
    .globl mmio_barrier
mmio_barrier:
    lui t0, 0x30000
    sw a0, 0xF8(t0)
    ret
"""


def stage4_link(obj, tools, tmp):
    clang, lld = tools
    stub_o = os.path.join(tmp, "stub.o")
    linked = os.path.join(tmp, "linked.elf")
    r = subprocess.run(
        [clang, "--target=riscv32-unknown-elf", "-march=rv32imac", "-x", "assembler",
         "-c", "-", "-o", stub_o],
        input=STUB_ASM, capture_output=True, text=True,
    )
    if r.returncode != 0:
        die(f"stage4: stub assembly failed: {r.stderr}")
    r = subprocess.run(
        [lld, "-m", "elf32lriscv", "-Ttext", hex(CODE), "-e", "wdg_status",
         "--no-relax", obj, stub_o, "-o", linked],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        die(f"stage4: real link failed (undefined symbols would show here): {r.stderr}")
    # Verify each patched call site lands on the right stub: decode the
    # auipc+jalr pair and compute its target.
    with open(linked, "rb") as f:
        elf = ELFFile(f)
        syms = {}
        for sec in elf.iter_sections():
            if sec["sh_type"] == "SHT_SYMTAB":
                for sym in sec.iter_symbols():
                    if sym.name:
                        syms[sym.name] = sym["st_value"]
        text = elf.get_section_by_name(".text")
        base, data = text["sh_addr"], text.data()
    stub_addrs = {syms["mmio_read32"], syms["mmio_write32"], syms["mmio_barrier"]}
    call_targets = []
    for off in range(0, len(data) - 4, 4):
        (auipc,) = struct.unpack_from("<I", data, off)
        if auipc & 0xFFF != 0x097:  # auipc ra
            continue
        (jalr,) = struct.unpack_from("<I", data, off + 4)
        if jalr & 0xFFF != 0x0E7 or (jalr >> 12) & 0x7 != 0 or (jalr >> 15) & 0x1F != 1:
            continue  # not `jalr ra, imm(ra)`
        hi = auipc >> 12
        lo = (jalr >> 20) & 0xFFF
        if lo >= 0x800:
            lo -= 0x1000
        target = (base + off + (hi << 12) + lo) & 0xFFFFFFFF
        call_targets.append(target)
    bad = [hex(t) for t in call_targets if t not in stub_addrs]
    if bad:
        die(f"stage4: patched auipc/jalr call(s) target {bad}, not the mmio stubs {sorted(hex(a) for a in stub_addrs)}")
    expected_sites = sum(EXPORTS.values())
    if len(call_targets) != expected_sites:
        die(f"stage4: found {len(call_targets)} patched call pairs, expected {expected_sites}")
    print(f"stage4 OK: real link (ld.lld) resolved both stubs; {len(call_targets)} call sites land on them")
    return linked, syms


def wasmtime_ground_truth():
    """Run every case in wasmtime with a Python mmio model; return results."""
    results = {}
    for fn, arglists in CASES.items():
        for args in arglists:
            mmio = dict(MMIO_INIT)

            store = wasmtime.Store()
            module = wasmtime.Module(store.engine, open(WAT).read())

            def _to_i32(v):
                return v - (1 << 32) if v >= (1 << 31) else v

            def mmio_read(caller, addr):
                a = addr & 0xFFFFFFFF
                return _to_i32(mmio.get(a - MMIO_BASE, 0))

            def mmio_write(caller, addr, val):
                a = addr & 0xFFFFFFFF
                mmio[a - MMIO_BASE] = val & 0xFFFFFFFF
                return _to_i32(val & 0xFFFFFFFF)

            i32 = wasmtime.ValType.i32()
            read_f = wasmtime.Func(
                store, wasmtime.FuncType([i32], [i32]), mmio_read, access_caller=True
            )
            write_f = wasmtime.Func(
                store, wasmtime.FuncType([i32, i32], [i32]), mmio_write, access_caller=True
            )

            def mmio_barrier(caller, val):
                mmio[0xF8] = val & 0xFFFFFFFF

            barrier_f = wasmtime.Func(
                store, wasmtime.FuncType([i32], []), mmio_barrier, access_caller=True
            )
            inst = wasmtime.Instance(store, module, [read_f, write_f, barrier_f])
            f = inst.exports(store)[fn]
            signed = [a - (1 << 32) if a >= (1 << 31) else a for a in args]
            ret = f(store, *signed) & 0xFFFFFFFF
            results[(fn, args)] = (ret, dict(mmio))
    return results


def stage5_execute(linked, syms, truth):
    with open(linked, "rb") as f:
        elf = ELFFile(f)
        segs = []
        for seg in elf.iter_segments():
            if seg["p_type"] == "PT_LOAD" and seg["p_memsz"] > 0:
                segs.append((seg["p_vaddr"], seg.data()))
    if not segs:
        die("stage5: linked image has no PT_LOAD segments")
    # Cover every loadable segment with 4K-aligned mappings.
    lo = min(v for v, _ in segs) & ~0xFFF
    hi = max(v + len(d) for v, d in segs)
    hi = (hi + 0xFFF) & ~0xFFF

    checked = 0
    for (fn, args), (want_ret, want_mmio) in truth.items():
        uc = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        uc.mem_map(lo, hi - lo)
        uc.mem_map(0x80000, 0x20000)  # stack
        if not (lo <= RET < hi):
            uc.mem_map(RET & ~0xFFF, 0x1000)
        uc.mem_map(MMIO_BASE, MMIO_SIZE)
        for vaddr, data in segs:
            uc.mem_write(vaddr, data)
        for off, val in MMIO_INIT.items():
            uc.mem_write(MMIO_BASE + off, struct.pack("<I", val))
        uc.reg_write(UC_RISCV_REG_SP, STK)
        uc.reg_write(UC_RISCV_REG_RA, RET)
        uc.reg_write(UC_RISCV_REG_A0, args[0])
        if len(args) > 1:
            uc.reg_write(UC_RISCV_REG_A1, args[1])
        uc.emu_start(syms[fn], RET, timeout=5_000_000, count=100_000)
        if uc.reg_read(UC_RISCV_REG_PC) != RET:
            die(f"stage5: {fn}{args} did not return (pc={uc.reg_read(UC_RISCV_REG_PC):#x})")
        got_ret = uc.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
        if got_ret != want_ret:
            die(f"stage5: {fn}{args}: rv32 returned {got_ret:#x}, wasmtime says {want_ret:#x}")
        for off in set(MMIO_INIT) | {k for k in want_mmio}:
            (got_w,) = struct.unpack("<I", bytes(uc.mem_read(MMIO_BASE + off, 4)))
            want_w = want_mmio.get(off, 0)
            if got_w != want_w:
                die(
                    f"stage5: {fn}{args}: mmio[{off:#x}] = {got_w:#x} after rv32 run, "
                    f"wasmtime says {want_w:#x}"
                )
        checked += 1
    print(f"stage5 OK: {checked} (export, input) cases execute bit-identical to wasmtime")


def main():
    if not os.path.exists(SYNTH):
        die(f"synth binary not found at {SYNTH} (set SYNTH=...)")
    tmp = tempfile.mkdtemp(prefix="synth871-")
    rv_obj = os.path.join(tmp, "wdg-rv.o")
    arm_obj = os.path.join(tmp, "wdg-arm.o")
    compile_obj(rv_obj, ["-b", "riscv", "--target", "esp32c3"])
    compile_obj(arm_obj, ["--target", "cortex-m3"])

    defined = stage1_completeness(rv_obj)
    stage2_reloc_readback(rv_obj, defined)
    stage3_arm_parity(arm_obj)

    tools = find_rv32_linker()
    if tools is None:
        print("stage4/5 SKIPPED: no RV32-capable clang+ld.lld on PATH "
              "(reloc read-back in stage2 remains the byte-level evidence)")
        print("PASS (stages 1-3)")
        return
    linked, syms = stage4_link(rv_obj, tools, tmp)
    truth = wasmtime_ground_truth()
    stage5_execute(linked, syms, truth)
    print("PASS: #871 external-call relocations verified (read-back + real link + execution)")


if __name__ == "__main__":
    main()
