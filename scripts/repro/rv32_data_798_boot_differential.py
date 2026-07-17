#!/usr/bin/env python3
"""#798 — RV32 active-data-segment shipping: FULL-BOOT differential.

End-to-end over the REAL artifacts, not a model of them: synth compiles a
module with OVERLAPPING active data segments to an RV32 object (`.wasm_data`
records), `synth riscv-runtime` emits the startup.c + linker.ld, clang+lld
build a bare-metal firmware, and unicorn boots it FROM `_reset` — so the
generated startup's record-copy loop (byte-granular, record order ⇒
later-wins) is what actually initializes linear memory. The exported reader's
result must match wasmtime.

This is the runtime half of the #798 gate; the compile-time half is the
VCR-VER-003 read-back (validate_served_image over the emitted records) and
the de-vacuated control_step differential.

Requires: clang with the riscv32 target (brew llvm), ld.lld, wasmtime +
unicorn + pyelftools in the venv. Missing tools are a LOUD failure, not a
skip — a gate that skips on an assumption is vacuous.

Run:
  /tmp/armv/bin/python scripts/repro/rv32_data_798_boot_differential.py
"""
import os
import shutil
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import UC_RISCV_REG_PC

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CLANG = os.environ.get("CLANG") or shutil.which("clang", path="/opt/homebrew/opt/llvm/bin") \
    or shutil.which("clang")
LLD = os.environ.get("LLD") or shutil.which("ld.lld")

# Overlapping segments: seg1 overwrites seg0's tail — the runtime image at 16
# is aa bb 11 22 ONLY if the startup copies records in declaration order.
WAT = r"""(module
  (memory 1)
  (data (i32.const 16) "\aa\bb\cc\dd")
  (data (i32.const 18) "\11\22")
  (func (export "get") (result i32) i32.const 16 i32.load))"""

MAIN_C = """extern unsigned get(void);
volatile unsigned result;
int main(void){ result = get(); return 0; }
"""


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        print(f"FAIL: {' '.join(str(c) for c in cmd)}\n{r.stdout}{r.stderr}")
        sys.exit(1)
    return r


def main():
    for tool, name in ((CLANG, "clang (riscv32-capable, e.g. brew llvm)"), (LLD, "ld.lld")):
        if not tool or not os.path.exists(tool):
            print(f"RV32 #798 BOOT ORACLE: FAIL — required tool missing: {name}")
            sys.exit(1)

    # wasmtime ground truth
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.encode())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    gt = inst.exports(store)["get"](store) & 0xFFFFFFFF

    d = tempfile.mkdtemp(prefix="rv32_798_boot_")
    wat = os.path.join(d, "module.wat")
    open(wat, "w").write(WAT)
    open(os.path.join(d, "main.c"), "w").write(MAIN_C)

    out = run([SYNTH, "compile", wat, "-b", "riscv", "--target", "rv32imac",
               "--all-exports", "--relocatable", "-o", os.path.join(d, "module.o")])
    if "Shipping 2 wasm data segment(s)" not in out.stdout + out.stderr:
        print("RV32 #798 BOOT ORACLE: FAIL — compile did not report shipping both segments")
        sys.exit(1)
    run([SYNTH, "riscv-runtime", "-o", d, "--linear-memory-size", "16384",
         "--stack-size", "4096"])

    cc = [CLANG, "-target", "riscv32-unknown-none-elf", "-march=rv32imac",
          "-mabi=ilp32", "-O1", "-c"]
    run(cc + [os.path.join(d, "startup.c"), "-o", os.path.join(d, "startup.o")])
    run(cc + [os.path.join(d, "main.c"), "-o", os.path.join(d, "main.o")])
    fw = os.path.join(d, "fw.elf")
    run([LLD, "-T", os.path.join(d, "linker.ld"), os.path.join(d, "startup.o"),
         os.path.join(d, "main.o"), os.path.join(d, "module.o"), "-o", fw])

    ef = ELFFile(open(fw, "rb"))
    syms = {s.name: s["st_value"]
            for s in ef.get_section_by_name(".symtab").iter_symbols() if s.name}
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(0x0, 0x10000)          # flash
    mu.mem_map(0x80000000, 0x10000)   # ram (presented zeroed — the scheme's assumption)
    for seg in ef.iter_segments():
        if seg["p_type"] == "PT_LOAD" and seg["p_filesz"]:
            mu.mem_write(seg["p_paddr"], seg.data())  # LMA: flash-resident images
    try:
        mu.emu_start(ef.header.e_entry, 0xFFFFFFFC, count=100_000)
    except UcError as e:
        print(f"RV32 #798 BOOT ORACLE: FAIL — boot faulted: {e} "
              f"pc=0x{mu.reg_read(UC_RISCV_REG_PC):x}")
        sys.exit(1)

    lin = bytes(mu.mem_read(syms["__linear_memory_base"] + 16, 4))
    res = int.from_bytes(mu.mem_read(syms["result"], 4), "little")
    print(f"linmem[16..20] after reset copy = {lin.hex()} (later-wins: aabb1122)")
    print(f"get() via full boot = 0x{res:08x}  wasmtime = 0x{gt:08x}")
    ok = lin == bytes.fromhex("aabb1122") and res == gt
    print("RV32 #798 BOOT ORACLE: PASS — the generated startup's record-copy "
          "loop serves the later-wins image" if ok
          else "RV32 #798 BOOT ORACLE: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
