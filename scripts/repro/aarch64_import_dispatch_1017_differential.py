#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 6
"""RQ-60-A64IMPORT (#1017, VCR-REACH-002 increment 1) — aarch64 import
dispatch execution differential vs wasmtime.

The top-ranked real-world aarch64 blocker (~121 of 805 modules, 88 of 101
components): a module that CALLS an imported function, or whose funcref table
HOLDS one, used to loud-decline wholesale. The fix is synth's own ARM
`--relocatable` #173/#197 contract ported: the import becomes an UNDEFINED
symbol under its wasm FIELD name (`SHN_UNDEF`, `STT_FUNC`, `GLOBAL`) that the
host linker resolves — the wasm2c/Wasker pattern.

What this harness proves, in both directions:

  * SYMTAB evidence (pyelftools, never disasm text — the rv32 empty-syms
    lesson): the import's field name is present, GLOBAL/STT_FUNC/SHN_UNDEF,
    and the `bl` site's R_AARCH64_CALL26 (283) — resp. the table trampoline's
    R_AARCH64_JUMP26 (282) — binds to exactly that symbol.
  * LINK + EXECUTE: this harness acts as the HOST — it places `.text`, appends
    its own A64 definitions of the imported functions, resolves every
    relocation itself, and runs the result under unicorn. A wrong reloc type,
    a wrong symbol, or a dropped site diverges from wasmtime.
  * wasmtime FIRST: every expected value comes from wasmtime executing the
    same module with the same host functions, so the table cannot drift.
  * the TRAP direction stays: an out-of-range table index must still trap
    exactly where wasmtime traps (import dispatch must not have loosened the
    call_indirect guards).
  * DECLINE HONESTY stays: the allowlist is imports-only — a module whose
    retained function calls a loud-DECLINED local callee must still refuse
    with the #1013 clean exit-1, never emit that callee as an undefined
    external. Probed with a real module (a `br_table` past the VCR-A64-CF-001
    threshold declines `func_0`; `func_1` calls it).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_import_dispatch_1017_differential.py
"""

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
)

HERE = Path(__file__).parent
WAT_CALL = HERE / "aarch64_import_call_1017.wat"
WAT_TABLE = HERE / "aarch64_import_table_1017.wat"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, STK, RET = 0x100000, 0x200000, 0x300000
M32 = (1 << 32) - 1
TRAP = "TRAP"

R_AARCH64_ADR_PREL_PG_HI21 = 275
R_AARCH64_ADD_ABS_LO12_NC = 277
R_AARCH64_JUMP26 = 282
R_AARCH64_CALL26 = 283

# The harness's own A64 definitions of the imported functions — the "host".
# Hand-encoded (verified against clang-assembled output of the same bodies):
#   host_add: add w0, w0, w1 ; ret
#   ext_inc:  add w0, w0, #1 ; ret
HOST_DEFS = {
    "host_add": [0x0B010000, 0xD65F03C0],
    "ext_inc": [0x11000400, 0xD65F03C0],
}

# (wat, entry, args, why). Expected values come from wasmtime, never from here.
CASES = [
    (WAT_CALL, "run", [37], "run(x) = host_add(x, 5) — the import is CALLED"),
    (WAT_CALL, "run", [0xFFFFFFFB], "wraparound through the import"),
    (WAT_TABLE, "run", [0, 41], "table slot 0 HOLDS the import -> ext_inc(41)"),
    (WAT_TABLE, "run", [1, 21], "table slot 1 is local -> local_dbl(21)"),
    (WAT_TABLE, "run", [2, 1], "index 2 out of range -> must still TRAP"),
    (WAT_TABLE, "run", [0xFFFFFFFF, 1], "unsigned OOB -> must still TRAP"),
]


def wasmtime_run(wat, fn, args):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(wat))
    store = wasmtime.Store(engine)
    linker = wasmtime.Linker(engine)
    i32 = wasmtime.ValType.i32()
    linker.define_func("env", "host_add", wasmtime.FuncType([i32, i32], [i32]),
                       lambda a, b: (a + b) & M32)
    linker.define_func("env", "ext_inc", wasmtime.FuncType([i32], [i32]),
                       lambda a: (a + 1) & M32)
    f = linker.instantiate(store, module).exports(store)[fn]
    conv = [struct.unpack("<i", struct.pack("<I", a & M32))[0] for a in args]
    try:
        return f(store, *conv) & M32
    except wasmtime.Trap:
        return TRAP


def compile_aarch64(wat, out):
    cmd = [SYNTH, "compile", str(wat), "-o", out, "-b", "aarch64",
           "--all-exports", "--relocatable"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"aarch64 compile of {wat.name} failed/skipped "
                 f"(pre-#1017 import-dispatch decline?):\n{r.stdout}\n{r.stderr}")


def check_symtab(path, import_name, want_reloc_type):
    """The #1017 contract, read from the symtab: the import's FIELD name is a
    GLOBAL STT_FUNC at SHN_UNDEF, and a relocation of the right type binds to
    it. Returns (elf-still-open-ok) or exits."""
    with open(path, "rb") as fh:
        f = ELFFile(fh)
        syms = list(f.get_section_by_name(".symtab").iter_symbols())
        idx = [i for i, s in enumerate(syms) if s.name == import_name]
        if len(idx) != 1:
            sys.exit(f"{path}: expected exactly one '{import_name}' symbol, "
                     f"found {len(idx)}")
        s = syms[idx[0]]
        if s["st_shndx"] != "SHN_UNDEF":
            sys.exit(f"{path}: '{import_name}' st_shndx = {s['st_shndx']}, "
                     f"not SHN_UNDEF — the import is not an undefined external")
        if s["st_info"]["bind"] != "STB_GLOBAL" or s["st_info"]["type"] != "STT_FUNC":
            sys.exit(f"{path}: '{import_name}' is "
                     f"{s['st_info']['bind']}/{s['st_info']['type']}, "
                     f"not GLOBAL/STT_FUNC")
        rela = f.get_section_by_name(".rela.text")
        if rela is None:
            sys.exit(f"{path}: no .rela.text")
        bound = [r for r in rela.iter_relocations()
                 if (r["r_info"] >> 32) == idx[0]]
        if not bound:
            sys.exit(f"{path}: no relocation binds to '{import_name}'")
        for r in bound:
            if r["r_info_type"] != want_reloc_type:
                sys.exit(f"{path}: reloc against '{import_name}' has type "
                         f"{r['r_info_type']}, want {want_reloc_type}")
        print(f"  symtab: '{import_name}' GLOBAL/STT_FUNC/SHN_UNDEF, "
              f"{len(bound)} reloc(s) type {want_reloc_type} bind to it")


def load_link_with_host(path):
    """Place `.text` at CODE, append the harness's OWN definitions of the
    imported functions after it, and resolve every relocation — undefined
    externals resolve to the harness definitions, exactly what a host linker
    does."""
    f = ELFFile(open(path, "rb"))
    sections = list(f.iter_sections())
    text_sec = f.get_section_by_name(".text")
    text = bytearray(text_sec.data())
    text_idx = sections.index(text_sec)

    # Append host definitions (4-byte aligned already; .text is whole words).
    host_addr = {}
    for name, words in HOST_DEFS.items():
        host_addr[name] = CODE + len(text)
        for w in words:
            text += struct.pack("<I", w)

    sym_addr, by_name = {}, {}
    for i, sy in enumerate(f.get_section_by_name(".symtab").iter_symbols()):
        if sy["st_shndx"] == text_idx:
            a = CODE + sy["st_value"]
        elif sy["st_shndx"] == "SHN_UNDEF" and sy.name in host_addr:
            a = host_addr[sy.name]  # the linker resolves the external
        else:
            continue
        sym_addr[i] = a
        if sy.name:
            by_name.setdefault(sy.name, a)

    rela = f.get_section_by_name(".rela.text")
    if rela is not None:
        for r in rela.iter_relocations():
            r_off = r["r_offset"]
            r_type = r["r_info_type"]
            target = sym_addr.get(r["r_info"] >> 32)
            if target is None:
                sys.exit(f"relocation against unplaced symbol "
                         f"(index {r['r_info'] >> 32})")
            site = CODE + r_off
            word = struct.unpack_from("<I", text, r_off)[0]
            s = target + r["r_addend"]
            if r_type in (R_AARCH64_CALL26, R_AARCH64_JUMP26):
                word = (word & 0xFC000000) | (((s - site) // 4) & 0x03FFFFFF)
            elif r_type == R_AARCH64_ADR_PREL_PG_HI21:
                v = ((s >> 12) - (site >> 12)) & 0x1FFFFF
                word &= ~((0x3 << 29) | (0x7FFFF << 5))
                word |= (v & 0x3) << 29
                word |= ((v >> 2) & 0x7FFFF) << 5
            elif r_type == R_AARCH64_ADD_ABS_LO12_NC:
                word = (word & ~(0xFFF << 10)) | ((s & 0xFFF) << 10)
            else:
                sys.exit(f"unexpected relocation type {r_type}")
            struct.pack_into("<I", text, r_off, word)
    return bytes(text), by_name


def emu_run(code, faddr, args):
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    for r, v in zip((UC_ARM64_REG_X0, UC_ARM64_REG_X1), args):
        mu.reg_write(r, v & M32)
    try:
        mu.emu_start(faddr, RET, count=100000)
    except UcError:
        return TRAP  # the guarded `brk #0`
    return mu.reg_read(UC_ARM64_REG_W0) & M32


def decline_honesty_probe():
    """A retained function calling a loud-DECLINED local callee must STILL
    refuse (exit 1, reason naming the symbol) — the imports allowlist must not
    have turned declined locals into silent externals. The callee declines via
    a `br_table` past the VCR-A64-CF-001 threshold; the caller relocates
    against it."""
    arms = "".join(f"(i32.const {i}) (return)" for i in range(40))
    table = " ".join(str(i % 2) for i in range(40))
    wat = f"""(module
  (func $declined (param i32) (result i32)
    (block (block
      (br_table {table} 0 (local.get 0)))
      (return (i32.const 7)))
    (i32.const 9))
  (func (export "caller") (param i32) (result i32)
    local.get 0
    call $declined))"""
    with tempfile.NamedTemporaryFile(suffix=".wat", mode="w", delete=False) as w:
        w.write(wat)
        wat_path = w.name
    with tempfile.NamedTemporaryFile(suffix=".o") as tmp:
        r = subprocess.run(
            [SYNTH, "compile", wat_path, "-o", tmp.name, "-b", "aarch64",
             "--all-exports", "--relocatable"],
            capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    os.unlink(wat_path)
    err = r.stdout + r.stderr
    if r.returncode == 0:
        print("FAIL: declined-local-callee module compiled — the allowlist "
              "leaked past imports")
        return False
    if "does not place" not in err or "func_0" not in err:
        print(f"FAIL: refusal did not name the declined symbol:\n{err}")
        return False
    print("  decline honesty: declined local callee still refuses "
          "(exit 1, names func_0) — allowlist is imports-only")
    return True


def main():
    fails = 0
    executions = 0

    print("== symtab contract ==")
    obj_call = "/tmp/aarch64_import_call_1017.o"
    obj_table = "/tmp/aarch64_import_table_1017.o"
    compile_aarch64(WAT_CALL, obj_call)
    compile_aarch64(WAT_TABLE, obj_table)
    check_symtab(obj_call, "host_add", R_AARCH64_CALL26)
    check_symtab(obj_table, "ext_inc", R_AARCH64_JUMP26)

    print("== execution differential (wasmtime first) ==")
    linked = {WAT_CALL: load_link_with_host(obj_call),
              WAT_TABLE: load_link_with_host(obj_table)}
    trap_cases = value_cases = 0
    for wat, fn, args, why in CASES:
        want = wasmtime_run(wat, fn, args)
        code, syms = linked[wat]
        got = emu_run(code, syms[fn], args)
        ok = got == want
        executions += 1
        if want == TRAP:
            trap_cases += 1
        else:
            value_cases += 1
        print(f"  {'ok  ' if ok else 'FAIL'} {wat.name}:{fn}{tuple(args)} "
              f"-> {got} (wasmtime: {want}) — {why}")
        if not ok:
            fails += 1

    # Non-vacuity: both directions must have been exercised.
    if trap_cases == 0 or value_cases == 0:
        print(f"VACUOUS: trap_cases={trap_cases} value_cases={value_cases}")
        return 1

    print("== decline honesty ==")
    if not decline_honesty_probe():
        fails += 1

    print(f"\nexecutions: {executions} ({value_cases} value, {trap_cases} trap)")
    if fails:
        print(f"RESULT: FAIL ({fails})")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
