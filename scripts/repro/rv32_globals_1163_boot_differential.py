#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 26
"""RQ-63-RVGLOBAL (#242, v0.63) — RV32 WASM globals: FULL-BOOT execution
differential against wasmtime.

RED before the lowering existed: on v0.62 every `global.get` declined
(`unsupported wasm op for RV32 skeleton: GlobalGet(..)`) — 132 modules of the
RQ-62-REACH census, the largest single blocker on any backend. This oracle
FAILED on that tree (the compile step is refused, so no vector reaches the
emulator and the declared floor is unmet as well) and PASSES once the
lowering ships. It is the instrument the reach increment is gated on.

# What is executed, and why it is shaped this way

synth emits the globals as a synth-EMITTED `.data` region (`__synth_globals`,
one dense slot per defined global carrying its decoded constant initializer)
that every `global.get`/`global.set` reaches through `lui`+`addi` against the
symbol (`R_RISCV_HI20` + `R_RISCV_LO12_I` — the RV32 twin of aarch64's
`adrp`+`add :lo12:`, #851). Nothing about that is observable from a raw
`.text` load: the relocations are unresolved, the region is unplaced, and
its initializer image is in flash until a startup copies it. So this oracle
does what a consumer does — links the object with clang+lld against synth's
own generated startup.c/linker.ld and boots the firmware FROM `_reset` under
unicorn, so the linker's placement and the startup's `.data` copy are what
put the globals where the code reads them. Each exported function is then
executed under emulation, in sequence, on that booted image; wasmtime runs the
same sequence on ONE instance so that `global.set` in step k is what step k+1
observes on both sides.

Three scenarios, each a fresh boot (state must not leak between them):
  init     — every global reads back its decoded initializer (the #1052
             dropped-initializer class, i64 both words, negative i32)
  mutate   — set/get, read-modify-write, i64 write via two i32 halves,
             i64 negate; an immutable global re-read after the writes
  pointer  — the `__stack_pointer` shape: a global feeding s11-relative
             load/store (push/pop through linear memory)

The floor counts unicorn `emu_start` calls: 3 boots + 23 export executions.
A wrong-slot, dropped-initializer, high-word-zeroed, write-to-flash or
copy-skipped defect fails a specific vector by name.

Decline honesty (compile-only, no emulation): a function touching an IMPORTED
global and a defined global with a NON-CONSTANT initializer must be refused
loudly — an accepted module that silently returns a wrong value is the shape
this release must not reintroduce.

Requires: clang with the riscv32 target, ld.lld, wasmtime + unicorn +
pyelftools. Missing tools are a LOUD failure, not a skip.

Run:
  SYNTH=./target/debug/synth python scripts/oracle_run.py \\
      scripts/repro/rv32_globals_1163_boot_differential.py
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
    UC_RISCV_REG_PC,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CLANG = (
    os.environ.get("CLANG")
    or shutil.which("clang", path="/opt/homebrew/opt/llvm/bin")
    or shutil.which("clang")
)
LLD = os.environ.get("LLD") or shutil.which("ld.lld")

WAT = "scripts/repro/rv32_globals_1163.wat"
FLASH, FLASH_SIZE = 0x0, 0x10000
RAM, RAM_SIZE = 0x80000000, 0x10000
RET = 0xFFFFF000  # return-address sentinel for export calls (mapped, never executed)

R_RISCV_HI20, R_RISCV_LO12_I, R_RISCV_LO12_S = 26, 27, 28
GLOBALS_SYM = "__synth_globals"
# Dense width-summed layout of the fixture's six globals (#643): 4+4+8+4+8+4.
EXPECTED_GLOBALS_BYTES = 32

MAIN_C = "int main(void) { return 0; }\n"

# (export, args, result kind) — `None` result kind = void export.
SCENARIOS = {
    "init": [
        ("get_a", (), "i32"),
        ("get_b", (), "i32"),
        ("get_c", (), "i64"),
        ("get_d", (), "i32"),
        ("get_e_lo", (), "i32"),
        ("get_e_hi", (), "i32"),
    ],
    "mutate": [
        ("set_a", (0x5A5A,), None),
        ("get_a", (), "i32"),
        ("bump_d", (5,), "i32"),
        ("bump_d", (-2,), "i32"),
        ("get_d", (), "i32"),
        ("set_c_parts", (0xDEADBEEF, 0x0BADF00D), None),
        ("get_c", (), "i64"),
        ("neg_e", (), None),
        ("get_e_lo", (), "i32"),
        ("get_e_hi", (), "i32"),
        ("get_b", (), "i32"),
    ],
    "pointer": [
        ("get_sp", (), "i32"),
        ("push", (11,), "i32"),
        ("push", (22,), "i32"),
        ("pop", (), "i32"),
        ("pop", (), "i32"),
        ("get_sp", (), "i32"),
    ],
}

# Decline-honesty probes: (label, wat, needle that MUST appear in stderr).
DECLINE_PROBES = [
    (
        "imported global access",
        r"""(module
  (import "env" "g" (global $g (mut i32)))
  (func (export "get") (result i32) global.get $g))""",
        "imported global",
    ),
    (
        "non-constant initializer",
        r"""(module
  (import "env" "base" (global $base i32))
  (global $g (mut i32) (global.get $base))
  (func (export "get") (result i32) global.get $g))""",
        "non-constant",
    ),
]


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        print(f"FAIL: {' '.join(str(c) for c in cmd)}\n{r.stdout}{r.stderr}")
        sys.exit(1)
    return r


def to_u32(v):
    return v & 0xFFFFFFFF


def to_i32(v):
    v = to_u32(v)
    return v - (1 << 32) if v & 0x80000000 else v


def check_object(obj_path):
    """Structural checks on synth's object: the globals region and its relocs
    exist and have the shape the lowering documents. Cheap, and each is a
    distinct way the emitted object could be wrong before a linker sees it."""
    with open(obj_path, "rb") as fh:
        f = ELFFile(fh)
        data = f.get_section_by_name(".data")
        if data is None:
            return "no .data section in the object (globals region not emitted)"
        if not (data["sh_flags"] & 0x1):
            return ".data lacks SHF_WRITE — a linker may place the globals in flash"
        if data["sh_size"] != EXPECTED_GLOBALS_BYTES:
            return (
                f".data is {data['sh_size']} bytes, expected the dense "
                f"{EXPECTED_GLOBALS_BYTES}-byte layout (#643 width-summed slots)"
            )
        st = f.get_section_by_name(".symtab")
        sym = next((s for s in st.iter_symbols() if s.name == GLOBALS_SYM), None)
        if sym is None:
            return f"{GLOBALS_SYM} symbol missing"
        if sym["st_info"]["type"] != "STT_OBJECT" or sym["st_size"] != EXPECTED_GLOBALS_BYTES:
            return f"{GLOBALS_SYM} is not an STT_OBJECT of {EXPECTED_GLOBALS_BYTES} bytes"
        rela = f.get_section_by_name(".rela.text")
        if rela is None:
            return "no .rela.text — the globals accesses carry no relocations"
        kinds = {}
        for r in rela.iter_relocations():
            name = st.get_symbol(r["r_info_sym"]).name
            if name == GLOBALS_SYM:
                kinds[r["r_info_type"]] = kinds.get(r["r_info_type"], 0) + 1
        if kinds.get(R_RISCV_HI20, 0) == 0 or kinds.get(R_RISCV_LO12_I, 0) == 0:
            return f"expected R_RISCV_HI20 + R_RISCV_LO12_I against {GLOBALS_SYM}, saw {kinds}"
        if kinds[R_RISCV_HI20] != kinds[R_RISCV_LO12_I]:
            return f"HI20/LO12_I pair count mismatch: {kinds}"
        print(
            f"  object: .data {data['sh_size']} B (SHF_WRITE), {GLOBALS_SYM} STT_OBJECT, "
            f"{kinds[R_RISCV_HI20]} HI20+LO12_I pairs"
        )
        return None


def build_firmware(d):
    wat = os.path.join(d, "module.wat")
    shutil.copyfile(WAT, wat)
    open(os.path.join(d, "main.c"), "w").write(MAIN_C)
    obj = os.path.join(d, "module.o")
    run([SYNTH, "compile", wat, "-b", "riscv", "--target", "rv32imac",
         "--all-exports", "--relocatable", "-o", obj])
    err = check_object(obj)
    if err:
        print(f"RV32 GLOBALS ORACLE: FAIL — object: {err}")
        sys.exit(1)
    run([SYNTH, "riscv-runtime", "-o", d, "--linear-memory-size", "16384",
         "--stack-size", "4096"])
    cc = [CLANG, "-target", "riscv32-unknown-none-elf", "-march=rv32imac",
          "-mabi=ilp32", "-O1", "-c"]
    run(cc + [os.path.join(d, "startup.c"), "-o", os.path.join(d, "startup.o")])
    run(cc + [os.path.join(d, "main.c"), "-o", os.path.join(d, "main.o")])
    fw = os.path.join(d, "fw.elf")
    run([LLD, "-T", os.path.join(d, "linker.ld"), os.path.join(d, "startup.o"),
         os.path.join(d, "main.o"), obj, "-o", fw])
    return fw


class Booted:
    """One unicorn instance booted from `_reset` up to (not into) `main`."""

    def __init__(self, fw):
        self.ef = ELFFile(open(fw, "rb"))
        self.syms = {
            s.name: s["st_value"]
            for s in self.ef.get_section_by_name(".symtab").iter_symbols()
            if s.name
        }
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        mu.mem_map(FLASH, FLASH_SIZE)
        mu.mem_map(RAM, RAM_SIZE)  # presented zeroed — the scheme's assumption
        mu.mem_map(RET & ~0xFFF, 0x1000)
        for seg in self.ef.iter_segments():
            if seg["p_type"] == "PT_LOAD" and seg["p_filesz"]:
                mu.mem_write(seg["p_paddr"], seg.data())  # LMA: flash-resident images
        self.mu = mu
        try:
            mu.emu_start(self.ef.header.e_entry, self.syms["main"], count=200_000)
        except UcError as e:
            print(f"RV32 GLOBALS ORACLE: FAIL — boot faulted: {e} "
                  f"pc=0x{mu.reg_read(UC_RISCV_REG_PC):x}")
            sys.exit(1)
        if mu.reg_read(UC_RISCV_REG_PC) != self.syms["main"]:
            print("RV32 GLOBALS ORACLE: FAIL — boot did not reach main")
            sys.exit(1)
        self.sp = mu.reg_read(UC_RISCV_REG_SP)
        self.s11 = mu.reg_read(UC_RISCV_REG_S11)
        if self.s11 != self.syms["__linear_memory_base"]:
            print("RV32 GLOBALS ORACLE: FAIL — startup left s11 != __linear_memory_base")
            sys.exit(1)

    def call(self, name, args, kind):
        mu = self.mu
        entry = self.syms.get(name)
        if entry is None:
            return None
        for reg, a in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1), args):
            mu.reg_write(reg, to_u32(a))
        mu.reg_write(UC_RISCV_REG_SP, self.sp)
        mu.reg_write(UC_RISCV_REG_S11, self.s11)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        mu.emu_start(entry, RET, count=100_000)
        if mu.reg_read(UC_RISCV_REG_PC) != RET:
            raise RuntimeError(f"{name}: did not return (pc=0x{mu.reg_read(UC_RISCV_REG_PC):x})")
        if kind is None:
            return "void"
        lo = mu.reg_read(UC_RISCV_REG_A0)
        if kind == "i64":
            return lo | (mu.reg_read(UC_RISCV_REG_A1) << 32)
        return lo


def wasmtime_scenario(engine, module, steps):
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    ex = inst.exports(store)
    out = []
    for name, args, kind in steps:
        r = ex[name](store, *[to_i32(a) for a in args])
        if kind is None:
            out.append("void")
        elif kind == "i64":
            out.append(r & 0xFFFFFFFFFFFFFFFF)
        else:
            out.append(to_u32(r))
    return out


def decline_probes(d):
    fails = 0
    for label, wat, needle in DECLINE_PROBES:
        p = os.path.join(d, "probe.wat")
        open(p, "w").write(wat)
        r = subprocess.run(
            [SYNTH, "compile", p, "-b", "riscv", "--target", "rv32imac",
             "--all-exports", "--relocatable", "-o", os.path.join(d, "probe.o")],
            capture_output=True, text=True,
        )
        ok = r.returncode != 0 and needle in (r.stdout + r.stderr)
        print(f"  decline[{label}]: rc={r.returncode} needle={needle!r} "
              f"{'OK' if ok else '*** ACCEPTED OR MIS-ATTRIBUTED ***'}")
        fails += 0 if ok else 1
    return fails


def main():
    for tool, name in ((CLANG, "clang (riscv32-capable, e.g. brew llvm)"), (LLD, "ld.lld")):
        if not tool or not os.path.exists(tool):
            print(f"RV32 GLOBALS ORACLE: FAIL — required tool missing: {name}")
            sys.exit(1)

    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    d = tempfile.mkdtemp(prefix="rv32_globals_1163_")
    fw = build_firmware(d)

    fails = executed = 0
    for scen, steps in SCENARIOS.items():
        want = wasmtime_scenario(engine, module, steps)
        booted = Booted(fw)
        gaddr = booted.syms.get(GLOBALS_SYM)
        if gaddr is None or not (RAM <= gaddr < RAM + RAM_SIZE):
            print(f"RV32 GLOBALS ORACLE: FAIL — {GLOBALS_SYM} not placed in RAM "
                  f"(addr={gaddr}); a global.set would write flash")
            sys.exit(1)
        print(f"scenario {scen}: {GLOBALS_SYM} @ 0x{gaddr:08x}")
        for (name, args, kind), w in zip(steps, want):
            try:
                g = booted.call(name, args, kind)
            except (UcError, RuntimeError) as e:
                print(f"  {name}{args}: FAULT {e}")
                fails += 1
                continue
            if g is None:
                print(f"  {name}{args}: SYMBOL MISSING — function skipped")
                fails += 1
                continue
            executed += 1
            ok = g == w
            fails += 0 if ok else 1
            fmt = (lambda v: v if v == "void" else f"0x{v:x}")
            print(f"  {name}{args}: synth={fmt(g)} wasmtime={fmt(w)} "
                  f"{'OK' if ok else '*** MISMATCH ***'}")

    print("\ndecline honesty:")
    fails += decline_probes(d)

    total = sum(len(s) for s in SCENARIOS.values())
    print(f"\nRV32-GLOBALS-1163 EMULATIONS={executed}/{total} (+{len(SCENARIOS)} boots)")
    if executed != total:
        print(f"FAIL: only {executed} of {total} vectors reached the emulator")
        sys.exit(1)
    print(
        "RESULT: PASS — every global read/write matches wasmtime on the booted image"
        if not fails
        else f"FAIL: {fails} check(s) disagree"
    )
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
