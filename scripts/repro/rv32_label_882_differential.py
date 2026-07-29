#!/usr/bin/env python3
"""#882 — RV32 `return`-inside-a-frame: label definition + reachable-join oracle.

gale's i2c-thin driver (v0.52.0, `-b riscv --target esp32c3 --all-exports
--relocatable`) hit `RISC-V function emit: undefined label 'Lend0'` on
`i2c_step`. Root cause: a mid-function `return` ABORTED the lowering walk
(`lower_seq` broke on `emitted_return`), so the frame-closing `end`s never
emitted their branch-target labels — and the REACHABLE code past a join
(an else-arm, or the code after a `br_if`-targeted `end`) was silently never
lowered. Loud skip pre-fix; the fix walks the dead region's control skeleton,
defines every label at its correct lexical position, and resumes lowering at
each reachable join. The ELF builder gained the #882 hard gate: a duplicate
label definition (last-wins rebinding = wrong-offset branch) is a hard error.

What this harness proves (each stage hard-fails on violation):
  1. SYNTHETIC SHAPES — `rv32_label_882.wat` (block-end br_if target past a
     return; then-arm return with reachable else; the exact nested i2c_step
     shape) compiles with ALL exports present. Pre-fix: all three skipped
     with "undefined label" (RED).
  2. SYNTHETIC EXECUTION — every (export, input) vector runs under unicorn
     (UC_ARCH_RISCV / RV32) bit-identical to wasmtime, covering both the
     return path and every resumed join path.
  3. REAL DRIVER — gale's pinned `i2c_thin_882.wasm` compiles with the full
     7-export set (`i2c_step` included — pre-fix it was the 1-of-7 skip).
  4. REAL-DRIVER EXECUTION (when an rv32 clang + ld.lld are available) —
     the object links against a 2-stub mmio register file and `i2c_step`
     runs under unicorn vs wasmtime ground truth for vectors covering the
     early-return guard, the return-terminated write path, and the resumed
     post-join path: return values AND the final mmio register file must be
     bit-identical.

Run (needs wasmtime + unicorn + pyelftools):
  /tmp/ci_env/bin/python scripts/repro/rv32_label_882_differential.py
Env: SYNTH=path-to-synth (default ./target/debug/synth).
Exits nonzero on any mismatch.
"""

import os
import shutil
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_A2,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/rv32_label_882.wat"
WASM = "scripts/repro/i2c_thin_882.wasm"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, LIN, RET, MMIO = 0x100000, 0x40000, 0x200000, 0x88000

# (export, args) — every synthetic shape, both the return path and every
# resumed-join path.
SYNTH_VECTORS = [
    ("f", (0,)),  # br_if not taken -> return path
    ("f", (1,)),  # br_if taken -> lands on the once-undefined Lend0
    ("f", (7,)),
    ("g", (0,)),  # else arm (reachable only after the fix resumes at Else)
    ("g", (1,)),  # then arm -> return
    ("g", (5,)),
    ("h", (0, 0)),  # inner fall-through -> return 3
    ("h", (0, 1)),  # inner br_if -> resumed post-join code -> return 5
    ("h", (1, 0)),  # outer br_if -> lands on outer end -> return 9
    ("h", (1, 1)),
    ("h", (2, 3)),
]

I2C_EXPORTS = {
    "i2c_ack_byte",
    "i2c_addr_ack",
    "i2c_configure",
    "i2c_is_complete",
    "i2c_start",
    "i2c_step",
    "i2c_stop",
}

# i2c_step(base, cmd, data) vectors: cmd > 0xBFFFFFFF (signed) takes the
# early-return -1 guard; bit29 clear takes the return-terminated write path
# (the path whose `return` killed the walk); bit29 set takes the code AFTER
# the inner block's end — the region that was silently never lowered.
I2C_VECTORS = [
    ("i2c_step", (MMIO, 0x00000000, 0x55)),  # guard -> -1
    ("i2c_step", (MMIO, 0x80000001, 0x55)),  # bit29 clear -> write path, return
    ("i2c_step", (MMIO, 0xA0000000, 0x7F)),  # bit29 set, v4<=1 -> config write + post-join
    ("i2c_step", (MMIO, 0xA0000002, 0x7F)),  # bit29 set, v4>1  -> post-join only
]
# Status register (base+20) must have bits 0x80|0x40 set so both poll loops
# exit; both sides start from the identical register file.
MMIO_INIT = {MMIO + 20: 0xFF}


def die(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_obj(src, out):
    r = subprocess.run(
        [SYNTH, "compile", src, "-b", "riscv", "--target", "esp32c3",
         "--all-exports", "--relocatable", "-o", out],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        die(f"synth compile {src} failed:\n{r.stdout}\n{r.stderr}")
    return r.stdout + r.stderr


def read_elf(path):
    with open(path, "rb") as fh:
        elf = ELFFile(fh)
        st = elf.get_section_by_name(".symtab")
        syms = {
            s.name: s["st_value"]
            for s in st.iter_symbols()
            if s.name and s["st_info"]["type"] == "STT_FUNC"
        }
        code = elf.get_section_by_name(".text").data()
    return syms, code


def run_unicorn(code, entry, args, mmio_init=None, count=20000):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    for base, size in [(CODE, 0x20000), (LIN, 0x20000), (MMIO, 0x10000), (RET, 0x1000)]:
        mu.mem_map(base, size)
    mu.mem_write(CODE, bytes(code))
    for addr, val in (mmio_init or {}).items():
        mu.mem_write(addr, val.to_bytes(4, "little"))
    mu.reg_write(UC_RISCV_REG_SP, 0x90000 + 0x8000)
    mu.reg_write(UC_RISCV_REG_S11, LIN)
    for reg, a in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_A2), args):
        mu.reg_write(reg, a & 0xFFFFFFFF)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(entry, RET, count=count)
    except UcError as e:
        return None, None, f"unicorn: {e}"
    return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF, mu, ""


def stage12_synthetic(tmp):
    obj = os.path.join(tmp, "label882.o")
    out = compile_obj(WAT, obj)
    if "skipping function" in out:
        die(f"stage1: synthetic fixture had skipped functions (RED shape):\n{out}")
    syms, code = read_elf(obj)
    missing = {"f", "g", "h"} - set(syms)
    if missing:
        die(f"stage1: exports missing from the object: {sorted(missing)}")
    print(f"stage1 OK: synthetic fixture compiled, exports {sorted(syms)}")

    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    def wt(name, args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[name](store, *args) & 0xFFFFFFFF

    fails = 0
    for name, args in SYNTH_VECTORS:
        gt = wt(name, args)
        res, _, err = run_unicorn(code, CODE + syms[name], args)
        ok = res == gt
        fails += 0 if ok else 1
        shown = res if res is not None else f"ERR({err})"
        print(f"  {name}{args} = {shown}  wasmtime={gt}  {'OK' if ok else 'FAIL'}")
    if fails:
        die(f"stage2: {fails} synthetic execution mismatch(es)")
    print(f"stage2 OK: {len(SYNTH_VECTORS)} synthetic vectors bit-identical to wasmtime")


def stage3_real_driver(tmp):
    obj = os.path.join(tmp, "i2c882.o")
    out = compile_obj(WASM, obj)
    if "skipping function" in out:
        die(f"stage3: real i2c-thin driver had skipped functions (the #882 RED):\n{out}")
    syms, _ = read_elf(obj)
    missing = I2C_EXPORTS - set(syms)
    if missing:
        die(f"stage3: driver exports missing (pre-fix: i2c_step): {sorted(missing)}")
    print(f"stage3 OK: real i2c-thin driver compiled 7/7 exports incl. i2c_step")
    return obj


def find_rv32_linker():
    clangs = [
        "/opt/homebrew/opt/llvm/bin/clang",
        "/usr/local/opt/llvm/bin/clang",
        shutil.which("clang"),
    ]
    llds = [
        shutil.which("ld.lld"),
        "/opt/homebrew/opt/llvm/bin/ld.lld",
        "/opt/homebrew/bin/ld.lld",
        "/usr/local/opt/llvm/bin/ld.lld",
    ]
    lld = next((c for c in llds if c and os.path.exists(c)), None)
    if lld is None:
        return None
    for clang in clangs:
        if not clang or not os.path.exists(clang):
            continue
        probe = subprocess.run(
            [clang, "--target=riscv32-unknown-elf", "-march=rv32imac", "-x",
             "assembler", "-c", "-", "-o", os.devnull],
            input="nop\n", capture_output=True, text=True,
        )
        if probe.returncode == 0:
            return clang, lld
    return None


# The mmio seam as a raw register file: read = lw from the passed address,
# write = sw to it. The wasmtime side models the identical register file in
# Python, so the final memory contents must agree bit-for-bit.
STUB_ASM = """
    .text
    .globl mmio_read32
mmio_read32:
    lw a0, 0(a0)
    ret
    .globl mmio_write32
mmio_write32:
    sw a1, 0(a0)
    ret
"""


def stage4_execute_real(obj, tools, tmp):
    clang, lld = tools
    stub_o = os.path.join(tmp, "stub.o")
    linked = os.path.join(tmp, "linked.elf")
    r = subprocess.run(
        [clang, "--target=riscv32-unknown-elf", "-march=rv32imac", "-x",
         "assembler", "-c", "-", "-o", stub_o],
        input=STUB_ASM, capture_output=True, text=True,
    )
    if r.returncode != 0:
        die(f"stage4: stub assembly failed: {r.stderr}")
    r = subprocess.run(
        [lld, "-m", "elf32lriscv", "-Ttext", hex(CODE), "-e", "i2c_step",
         "--no-relax", obj, stub_o, "-o", linked],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        die(f"stage4: real link failed: {r.stderr}")
    with open(linked, "rb") as fh:
        elf = ELFFile(fh)
        syms = {}
        for sec in elf.iter_sections():
            if sec["sh_type"] == "SHT_SYMTAB":
                for sym in sec.iter_symbols():
                    if sym.name:
                        syms[sym.name] = sym["st_value"]
        text_sec = elf.get_section_by_name(".text")
        base, code = text_sec["sh_addr"], text_sec.data()
    if base != CODE:
        die(f"stage4: .text linked at {base:#x}, expected {CODE:#x}")

    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WASM)

    def wt(name, args):
        store = wasmtime.Store(engine)
        regfile = dict(MMIO_INIT)

        def mmio_read32(addr):
            return regfile.get(addr & 0xFFFFFFFF, 0)

        def mmio_write32(addr, val):
            regfile[addr & 0xFFFFFFFF] = val & 0xFFFFFFFF

        read_t = wasmtime.FuncType([wasmtime.ValType.i32()], [wasmtime.ValType.i32()])
        write_t = wasmtime.FuncType([wasmtime.ValType.i32(), wasmtime.ValType.i32()], [])
        imports = []
        for imp in module.imports:
            if imp.name == "mmio_read32":
                imports.append(wasmtime.Func(store, read_t, mmio_read32))
            elif imp.name == "mmio_write32":
                imports.append(wasmtime.Func(store, write_t, mmio_write32))
            else:
                die(f"stage4: unexpected import {imp.module}::{imp.name}")
        inst = wasmtime.Instance(store, module, imports)
        ret = inst.exports(store)[name](store, *args) & 0xFFFFFFFF
        return ret, regfile

    fails = 0
    for name, args in I2C_VECTORS:
        gt, gt_regs = wt(name, args)
        res, mu, err = run_unicorn(code, syms[name], args, MMIO_INIT)
        if res is None:
            print(f"  {name}{args} = ERR({err})  wasmtime={gt:#x}  FAIL")
            fails += 1
            continue
        ok = res == gt
        # Register-file agreement: every address either side touched.
        for addr in sorted(set(gt_regs) | set(MMIO_INIT)):
            uc_val = int.from_bytes(mu.mem_read(addr, 4), "little")
            if uc_val != gt_regs.get(addr, 0):
                ok = False
                print(f"    regfile[{addr:#x}]: unicorn={uc_val:#x} wasmtime={gt_regs.get(addr, 0):#x}")
        fails += 0 if ok else 1
        print(f"  {name}{args} = {res:#010x}  wasmtime={gt:#010x}  {'OK' if ok else 'FAIL'}")
    if fails:
        die(f"stage4: {fails} real-driver execution mismatch(es)")
    print(f"stage4 OK: linked i2c_step executes bit-identical to wasmtime "
          f"({len(I2C_VECTORS)} vectors, return values + mmio register file)")


def main():
    tmp = tempfile.mkdtemp(prefix="rv32_882_")
    stage12_synthetic(tmp)
    obj = stage3_real_driver(tmp)
    tools = find_rv32_linker()
    if tools:
        stage4_execute_real(obj, tools, tmp)
    else:
        print("stage4 SKIP: no rv32-capable clang+ld.lld on PATH (stages 1-3 still gate)")
    print("\nRV32 label/return #882 ORACLE: PASS")


if __name__ == "__main__":
    main()
