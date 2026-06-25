#!/usr/bin/env python3
"""VCR-RA RV32 lever (#472 step 2, epic #242) — EXECUTION-validate const-addr-fold.

`SYNTH_RV_ADDR_FOLD=1` folds a constant memory address into the access immediate
off s11: `addi a,zero,ADDR; add tmp,s11,a; sw v,off(tmp)` -> `sw v,(ADDR+off)(s11)`,
dropping two instructions per constant-address access. The RV32 path has no cargo
byte-gate, so EXECUTION is the oracle: this harness compiles the field-initializer
fixture (7 constant-address stores) in BOTH flag states, runs `init_fields` under
unicorn (UC_ARCH_RISCV) with s11 = the linear-memory base, and asserts the
resulting MEMORY is bit-identical to wasmtime ground truth (the fixture writes
memory and returns nothing, so memory is the observable).

NON-VACUITY: the flag-on `.text` must be strictly smaller (each fold drops the
`addi`+`add` pair), else the fold did not fire.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/const_addr_fold_riscv_differential.py
Exits nonzero on any mismatch or vacuity failure.
"""
import os
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import UC_RISCV_REG_RA, UC_RISCV_REG_S11, UC_RISCV_REG_SP

WAT = "scripts/repro/redundant_base_materialization.wat"
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000
# Fields written by init_fields: (wasm_addr, width_bytes).
FIELDS = [(0, 4), (4, 4), (8, 4), (12, 2), (14, 2), (16, 1), (17, 1)]


def compile_elf(out, fold):
    env = {"PATH": "/usr/bin:/bin"}
    if fold:
        env["SYNTH_RV_ADDR_FOLD"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", WAT, "-o", out, "-b", "riscv", "-t", "rv32imac",
         "--all-exports", "--relocatable"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (fold={fold}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] - base
    return code, base, syms


def run_rv(code, base, fa):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_RISCV_REG_SP, STK)
    mu.reg_write(UC_RISCV_REG_S11, LIN)  # s11 = __linear_memory_base
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + (fa & ~1) - base, RET, count=4000)
    except UcError as e:
        return f"ERR:{e}"
    out = {}
    for (off, w) in FIELDS:
        out[off] = int.from_bytes(mu.mem_read(LIN + off, w), "little")
    return out


def wasm_mem():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WAT, "rb").read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    inst.exports(store)["init_fields"](store)
    data = inst.exports(store)["memory"].read(store, 0, 64)
    return {off: int.from_bytes(data[off:off + w], "little") for (off, w) in FIELDS}


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    off_elf, on_elf = "/tmp/caf_off.o", "/tmp/caf_on.o"
    compile_elf(off_elf, False)
    compile_elf(on_elf, True)
    off_code, off_base, off_syms = load(off_elf)
    on_code, on_base, on_syms = load(on_elf)

    gt = wasm_mem()
    r_off = run_rv(off_code, off_base, off_syms["init_fields"])
    r_on = run_rv(on_code, on_base, on_syms["init_fields"])
    fails = 0
    ok = isinstance(r_off, dict) and isinstance(r_on, dict) and r_off == gt and r_on == gt
    fails += 0 if ok else 1
    print(f"init_fields: off={'ok' if isinstance(r_off, dict) else r_off} "
          f"on={'ok' if isinstance(r_on, dict) else r_on} vs wasmtime "
          f"{'MATCH' if ok else 'MISMATCH'}")
    if not ok:
        print(f"  off={r_off}\n  on ={r_on}\n  wt ={gt}")

    off_len, on_len = len(off_code), len(on_code)
    if not on_len < off_len:
        print(f"VACUOUS: flag-on .text ({on_len}B) not < flag-off ({off_len}B) "
              "— const-addr fold did not fire")
        fails += 1
    else:
        print(f"\n.text {off_len}B -> {on_len}B (-{off_len - on_len}B): "
              f"~{(off_len - on_len) // 4} instruction(s) folded across 7 const-addr stores")

    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
