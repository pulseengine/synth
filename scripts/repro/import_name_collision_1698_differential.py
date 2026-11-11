#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 39
"""RQ-91-NAMECOLL (#1698): a called import's object symbol must be its own.
This is an execution differential against wasmtime, with a symbol-table pin,
on every backend that turns an import call into a symbol.

THE DEFECT (exit 0, no diagnostic). Every object builder rewrites an import
call's `func_N` label to the import's wasm FIELD name (#173/#197/#871/#1017)
and then resolved that name in the namespace of the object's OWN
definitions, where a definition won. So

    (import "env" "get" (func $imp (result i32)))
    (func (export "get") (result i32) i32.const 7)
    (func (export "use_import") (result i32) call $imp)

bound `use_import`'s call to the export `get` and emitted no undefined
symbol. `use_import()` returned 7, where wasmtime with a host `env.get`
returns the host's value. Measured on main 52add192 on ARM Thumb-2 (relocatable
and the `--cortex-m` request, which silently produces the same ET_REL for an
import-carrying module), ARM A32 (cortex-r5), RV32 and AArch64. The same held
for an import named after a `func_N` label, after `__synth_globals` (a call
into DATA), after the AArch64 funcref table, after an `__aeabi_*` helper synth
itself calls, and for two imports of one field from different modules.

THE FIX is a refusal (`synth_core::import_symbols`), never a renaming: the
plain field name is the embedder ABI, so every non-colliding object keeps its
bytes.

WHAT THIS ORACLE CHECKS
  * REFUSE legs. Each collision class, on every config where it compiled on
    52add192, must exit non-zero, name the import and the symbol, and write
    no object. On 52add192 these legs compile, and the #1698 module is also
    executed to show the wrong value.
  * MATCH legs, executed. This harness is the HOST LINKER: it places `.text`,
    appends a host stub for each `SHN_UNDEF` symbol (keyed by the import
    field), resolves every relocation through the object's OWN symbol table
    as `ld` does (a defined symbol binds to its definition, an undefined one
    to the stub), and runs each export under unicorn against wasmtime with
    the same host functions. Covered: the paired control (the #1698 module
    with the export renamed); an import field equal to another import's
    `func_M` label and an export named `func_0` (both bound wrongly on ARM
    at 52add192 and correctly now); a declared but UNCALLED import beside a
    same-named export (must still compile: only a called import becomes a
    symbol); and one `(module, field)` imported twice (one host function,
    which must not refuse).
  * SYMBOL PIN (pyelftools, by symtab, never disasm text). In every MATCH
    object each import field is `SHN_UNDEF`/`STB_GLOBAL`, and every call
    relocation to it has the ISA's call type (R_ARM_THM_CALL /
    R_ARM_CALL / R_RISCV_CALL_PLT / R_AARCH64_CALL26) and names that
    undefined symbol.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/import_name_collision_1698_differential.py
"""

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (UC_ARCH_ARM, UC_ARCH_ARM64, UC_ARCH_RISCV, UC_MODE_ARM,
                     UC_MODE_RISCV32, UC_MODE_THUMB, Uc)
from unicorn import arm64_const as A64
from unicorn import arm_const as A
from unicorn import riscv_const as RV

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
TEXT, STUB, STACK, SENT = 0x10000, 0x20000, 0x80000, 0x30000

CONFIGS = {
    "m4": ("thumb", ["--target", "cortex-m4", "--relocatable"]),
    "m4-cortexm": ("thumb", ["--target", "cortex-m4", "--cortex-m"]),
    "m4f": ("thumb", ["--target", "cortex-m4f", "--relocatable"]),
    "npa": ("thumb", ["--target", "cortex-m4", "--relocatable", "--native-pointer-abi"]),
    "r5": ("a32", ["--target", "cortex-r5", "--relocatable"]),
    "rv32": ("rv32", ["-b", "riscv", "--relocatable"]),
    "a64": ("a64", ["-b", "aarch64", "--relocatable"]),
}
CALL_RELOC = {"thumb": 10, "a32": 28, "rv32": 19, "a64": 283}
FIVE = ["m4", "m4-cortexm", "r5", "rv32", "a64"]
FOUR = ["m4", "r5", "rv32", "a64"]

NC = """(module
  (import "env" "get" (func $imp (result i32)))
  (func (export "get") (result i32) i32.const 7)
  (func (export "use_import") (result i32) call $imp))"""

# --- MATCH legs: (name, wat, configs, host {(module, field): value}, exports)
MATCH = [
    ("control-renamed-export", NC.replace('(export "get")', '(export "get7")'),
     FIVE, {("env", "get"): 42}, ["use_import", "get7"]),
    ("import-field-is-another-imports-label",
     """(module
  (import "env" "func_1" (func $a (result i32)))
  (import "env" "x" (func $b (result i32)))
  (func (export "use_a") (result i32) call $a)
  (func (export "use_b") (result i32) call $b))""",
     FOUR, {("env", "func_1"): 42, ("env", "x"): 99}, ["use_a", "use_b"]),
    ("export-named-func_0",
     """(module
  (import "env" "get" (func $imp (result i32)))
  (func (export "func_0") (result i32) i32.const 7)
  (func (export "use_import") (result i32) call $imp))""",
     FOUR, {("env", "get"): 42}, ["use_import", "func_0"]),
    ("uncalled-import-beside-same-named-export",
     """(module
  (import "env" "get" (func $imp (result i32)))
  (func (export "get") (result i32) i32.const 7))""",
     FIVE, {("env", "get"): 42}, ["get"]),
    ("same-module-and-field-twice",
     """(module
  (import "env" "get" (func $a (result i32)))
  (import "env" "get" (func $b (result i32)))
  (func (export "use_a") (result i32) call $a)
  (func (export "use_b") (result i32) call $b))""",
     FOUR, {("env", "get"): 42}, ["use_a", "use_b"]),
]

# --- REFUSE legs: (name, wat, configs, extra flags, needles in the diagnostic)
REFUSE = [
    ("import-equals-own-export", NC, FIVE, [], ["`env`.`get`", "symbol `get`", "#1698"]),
    ("single-function-shim", """(module
  (import "env" "get" (func $imp (result i32)))
  (func (export "get") (result i32) call $imp i32.const 1 i32.add))""",
     ["m4"], ["--func-name", "get"], ["`env`.`get`", "symbol `get`"]),
    ("import-equals-func_N-label", """(module
  (import "env" "func_1" (func $imp (result i32)))
  (func $helper (result i32) i32.const 7)
  (func (export "use_import") (result i32) call $imp)
  (func (export "h") (result i32) call $helper))""",
     FOUR, [], ["`env`.`func_1`", "symbol `func_1`"]),
    ("same-field-two-modules", """(module
  (import "a" "get" (func $a (result i32)))
  (import "b" "get" (func $b (result i32)))
  (func (export "use_a") (result i32) call $a)
  (func (export "use_b") (result i32) call $b))""",
     FOUR, [], ["`a`.`get` and `b`.`get`", "symbol `get`"]),
    ("import-equals-__synth_globals", """(module
  (import "env" "__synth_globals" (func $imp (result i32)))
  (global $g (mut i32) (i32.const 0))
  (func (export "use_import") (result i32) call $imp)
  (func (export "bump") (result i32)
    global.get $g i32.const 1 i32.add global.set $g global.get $g))""",
     ["npa", "rv32", "a64"], [], ["`env`.`__synth_globals`", "symbol `__synth_globals`"]),
    ("import-equals-aeabi-helper", """(module
  (import "env" "__aeabi_l2f" (func $imp (result i32)))
  (func (export "use_import") (result i32) call $imp)
  (func (export "cv") (param i64) (result f32) local.get 0 f32.convert_i64_s))""",
     ["m4f"], [], ["`env`.`__aeabi_l2f`", "different purpose"]),
    ("table-slot-import-equals-export", """(module
  (type $t (func (result i32)))
  (import "env" "get" (func $imp (result i32)))
  (table 2 funcref)
  (elem (i32.const 0) $imp $own)
  (func $own (export "get") (result i32) i32.const 7)
  (func (export "ci") (param i32) (result i32) local.get 0 call_indirect (type $t)))""",
     ["a64"], [], ["`env`.`get`", "symbol `get`"]),
    ("table-slot-import-equals-__synth_func_table", """(module
  (type $t (func (result i32)))
  (import "env" "__synth_func_table" (func $imp (result i32)))
  (table 1 funcref)
  (elem (i32.const 0) $imp)
  (func (export "ci") (param i32) (result i32) local.get 0 call_indirect (type $t)))""",
     ["a64"], [], ["`env`.`__synth_func_table`", "symbol `__synth_func_table`"]),
]

STUB_CODE = {
    "thumb": lambda v: struct.pack("<HH", 0x2000 | v, 0x4770),
    "a32": lambda v: struct.pack("<II", 0xE3A00000 | v, 0xE12FFF1E),
    "rv32": lambda v: struct.pack("<II", (v << 20) | (10 << 7) | 0x13, 0x00008067),
    "a64": lambda v: struct.pack("<II", 0x52800000 | (v << 5), 0xD65F03C0),
}

fails = []
checks = 0


def compile_(wat_path, out, flags, extra=()):
    if "--func-name" not in extra:
        extra = ["--all-exports", *extra]
    r = subprocess.run([SYNTH, "compile", str(wat_path), *extra, *flags, "-o", str(out)],
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def wasmtime_values(wat, host, exports):
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    mod = wasmtime.Module(eng, wat)
    ft = wasmtime.FuncType([], [wasmtime.ValType.i32()])
    imports = [wasmtime.Func(st, ft, (lambda v: (lambda: v))(host[(i.module, i.name)]))
               for i in mod.imports]
    inst = wasmtime.Instance(st, mod, imports)
    return {e: inst.exports(st)[e](st) & 0xFFFFFFFF for e in exports}


def thumb_bl(P, S):
    off = (S & ~1) - (P + 4)
    s = (off >> 24) & 1
    j1 = (~(((off >> 23) & 1) ^ s)) & 1
    j2 = (~(((off >> 22) & 1) ^ s)) & 1
    return struct.pack("<HH", 0xF000 | (s << 10) | ((off >> 12) & 0x3FF),
                       0xD000 | (j1 << 13) | (j2 << 11) | ((off >> 1) & 0x7FF))


def link(path, isa, field_value):
    """Host-link: resolve every relocation through the object's own symtab."""
    pins = []
    with open(path, "rb") as f:
        e = ELFFile(f)
        text = bytearray(e.get_section_by_name(".text").data())
        symtab = next(s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        syms = list(symtab.iter_symbols())
        stubs = {}
        for s in syms:
            if s.name and s["st_shndx"] == "SHN_UNDEF":
                if s.name not in field_value:
                    raise RuntimeError(f"undefined symbol {s.name!r} has no host definition")
                stubs[s.name] = STUB + 0x40 * len(stubs)
                pins.append((s.name, s["st_info"]["bind"]))

        def addr(s):
            if s["st_shndx"] == "SHN_UNDEF":
                return stubs[s.name]
            v = s["st_value"]
            return TEXT + (v & ~1 if isa == "thumb" else v)

        rel = next((s for s in e.iter_sections()
                    if s["sh_type"] in ("SHT_REL", "SHT_RELA") and s.name.endswith(".text")), None)
        calls = []
        for r in (rel.iter_relocations() if rel else []):
            s = syms[r["r_info_sym"]]
            t, o = r["r_info_type"], r["r_offset"]
            P, S = TEXT + o, addr(s)
            calls.append((t, s.name, s["st_shndx"] == "SHN_UNDEF"))
            if t == 10:
                text[o:o + 4] = thumb_bl(P, S)
            elif t == 28:
                w = struct.unpack_from("<I", text, o)[0]
                struct.pack_into("<I", text, o, (w & 0xFF000000) | (((S - (P + 8)) >> 2) & 0xFFFFFF))
            elif t == 19:
                off = S - P
                hi = (off + 0x800) >> 12
                lo = off - (hi << 12)
                au, jr = struct.unpack_from("<II", text, o)
                struct.pack_into("<II", text, o, (au & 0xFFF) | ((hi & 0xFFFFF) << 12),
                                 (jr & 0xFFFFF) | ((lo & 0xFFF) << 20))
            elif t == 283:
                w = struct.unpack_from("<I", text, o)[0]
                struct.pack_into("<I", text, o, (w & 0xFC000000) | (((S - P) >> 2) & 0x3FFFFFF))
            else:
                raise RuntimeError(f"unhandled relocation type {t}")
        funcs = {s.name: s["st_value"] & ~1 for s in syms
                 if s["st_info"]["type"] == "STT_FUNC" and s["st_shndx"] != "SHN_UNDEF"}
    return bytes(text), stubs, funcs, pins, calls


def emulate(isa, text, stubs, field_value, faddr):
    arch = {"thumb": (UC_ARCH_ARM, UC_MODE_THUMB), "a32": (UC_ARCH_ARM, UC_MODE_ARM),
            "rv32": (UC_ARCH_RISCV, UC_MODE_RISCV32), "a64": (UC_ARCH_ARM64, UC_MODE_ARM)}[isa]
    mu = Uc(*arch)
    for base in (TEXT, STUB, SENT, STACK - 0x10000):
        mu.mem_map(base, 0x10000)
    mu.mem_write(TEXT, text)
    for name, a in stubs.items():
        mu.mem_write(a, STUB_CODE[isa](field_value[name]))
    start = TEXT + faddr
    if isa in ("thumb", "a32"):
        t = 1 if isa == "thumb" else 0
        mu.reg_write(A.UC_ARM_REG_SP, STACK - 0x100)
        mu.reg_write(A.UC_ARM_REG_LR, SENT | t)
        mu.emu_start(start | t, SENT, count=10000)
        return mu.reg_read(A.UC_ARM_REG_R0) & 0xFFFFFFFF
    if isa == "rv32":
        mu.reg_write(RV.UC_RISCV_REG_SP, STACK - 0x100)
        mu.reg_write(RV.UC_RISCV_REG_RA, SENT)
        mu.emu_start(start, SENT, count=10000)
        return mu.reg_read(RV.UC_RISCV_REG_A0) & 0xFFFFFFFF
    mu.reg_write(A64.UC_ARM64_REG_SP, STACK - 0x100)
    mu.reg_write(A64.UC_ARM64_REG_LR, SENT)
    mu.emu_start(start, SENT, count=10000)
    return mu.reg_read(A64.UC_ARM64_REG_W0) & 0xFFFFFFFF


def run_match(td):
    global checks
    for name, wat, cfgs, host, exports in MATCH:
        src = td / f"{name}.wat"
        src.write_text(wat)
        want = wasmtime_values(wat, host, exports)
        field_value = {f: v for (_, f), v in host.items()}
        for c in cfgs:
            isa, flags = CONFIGS[c]
            out = td / f"{name}.{c}.o"
            rc, log = compile_(src, out, flags)
            if rc != 0:
                fails.append(f"match/{name}/{c}: must compile, rc {rc}: {log.strip()[-240:]}")
                continue
            text, stubs, funcs, pins, calls = link(out, isa, field_value)
            # SYMBOL PIN: every called import is a GLOBAL SHN_UNDEF symbol and
            # every call relocation naming an import field targets it.
            for sym, bind in pins:
                if bind != "STB_GLOBAL":
                    fails.append(f"pin/{name}/{c}: {sym} is {bind}, want STB_GLOBAL")
            for t, sym, undef in calls:
                if sym in field_value and (not undef or t != CALL_RELOC[isa]):
                    fails.append(f"pin/{name}/{c}: reloc type {t} -> {sym} undef={undef}")
            called = {s for _, s, _ in calls if s in field_value}
            if called - set(stubs):
                fails.append(f"pin/{name}/{c}: called import(s) {called - set(stubs)} not SHN_UNDEF")
            got = {}
            for ex in exports:
                got[ex] = emulate(isa, text, stubs, field_value, funcs[ex])
                checks += 1
                if got[ex] != want[ex]:
                    fails.append(f"match/{name}/{c}: {ex}() = {got[ex]}, wasmtime {want[ex]}")
            print(f"  [match]  {name:42} {c:10} {got} wasmtime {want} undef={sorted(stubs)}")


def run_refuse(td):
    global checks
    for name, wat, cfgs, extra, needles in REFUSE:
        src = td / f"{name}.wat"
        src.write_text(wat)
        for c in cfgs:
            isa, flags = CONFIGS[c]
            out = td / f"{name}.{c}.o"
            rc, log = compile_(src, out, flags, extra)
            checks += 1
            if rc == 0:
                msg = f"refuse/{name}/{c}: compiled (rc 0), must refuse"
                if name == "import-equals-own-export":
                    try:
                        text, stubs, funcs, _, _ = link(out, isa, {"get": 42})
                        v = emulate(isa, text, stubs, {"get": 42}, funcs["use_import"])
                        msg += f"; use_import() = {v}, wasmtime 42"
                    except Exception as ex:  # report, never mask the red
                        msg += f"; could not execute: {ex}"
                fails.append(msg)
                print(f"  [refuse] {name:42} {c:10} COMPILED")
                continue
            missing = [n for n in needles if n not in log]
            if missing:
                fails.append(f"refuse/{name}/{c}: rc {rc} but diagnostic lacks {missing}: {log.strip()[-240:]}")
            if out.exists():
                fails.append(f"refuse/{name}/{c}: refused but wrote {out.name}")
            print(f"  [refuse] {name:42} {c:10} rc={rc}")


def main():
    print("RQ-91-NAMECOLL (#1698) import-symbol collision differential")
    with tempfile.TemporaryDirectory() as d:
        td = Path(d)
        run_match(td)
        run_refuse(td)
    print(f"RQ-91-NAMECOLL: {checks} checks, {len(fails)} failure(s)")
    for f in fails:
        print(f"  FAIL {f}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
