#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 42
"""RQ-91-IMPGLOBAL (#1676) — an imported global no longer shifts every defined
global's slot. Execution differential against wasmtime on the three ARM
paths that lay out a globals table.

THE DEFECT (exit 0, no diagnostic, every path below). Imported globals take
the LEADING wasm global indices, so `global.get i` names import `i` when
`i < num_imported_globals`. The ARM selector addresses the table in that FULL
index space (`global_slot_offset`, the sum of the widths of globals `0..i`),
but the producers laid it out by DEFINED index:

  * `--relocatable --native-pointer-abi` (gale's path): `__synth_globals`
    slots were written at `defined_index * 4`, the stack-pointer global was
    identified by its defined index, so with one import every defined global
    read its NEIGHBOUR's slot and the stack-pointer rebase landed on the
    IMPORT (the real stack pointer was read raw, unrebased);
  * the self-contained Cortex-M image: the R9 table startup materializes
    (`globals_table_words`) started at the first DEFINED global;
  * plain `--relocatable`: the slot-width table was indexed by defined
    index, so a wide (i64) global after an import was addressed at the wrong
    offset with the wrong width, against the documented embedder contract.

An imported global's own value is supplied at instantiation; no ARM output
binds it, so a function that touches one is now REFUSED (`IMPORTED-GLOBAL`),
as aarch64 already refuses (substrate.rs). Unreferenced imports refuse
nothing — they only position the defined globals.

LEGS
  npa    hand-linked `--relocatable --native-pointer-abi` object (the
         npa_const_addr_differential linker: .text/.data/.bss at separate
         bases, R11 = 0), defined globals after 1 and 2 imports, a mutable
         global set/get, the stack-pointer read, and a no-import control.
  self   the self-contained Cortex-M image booted through its own
         Reset_Handler (the #1189 boot-sweep harness), i32 and i64 defined
         globals after imports, set/get.
  reloc  plain `--relocatable --embedder-global-init`: the harness IS the
         embedder and seeds R9 exactly as docs/embedder-abi-relocatable-arm.md
         states (each global's init at R9 + its slot offset, slot offsets the
         dense sum of widths in the full index space).
  refuse every path refuses a function that reads or writes an import, with
         `IMPORTED-GLOBAL`, and writes no object; an unreferenced import
         compiles.

Red on eab66646 (v0.90.0 + planning): 14 of the 32 compared values wrong
(npa 5, self 7, reloc 2) and all 4 refusal legs compiled the import read
silently, exit 0. Green on the fix: 40 checks, 0 failures. Run:
  SYNTH=./target/debug/synth python3 scripts/repro/imported_global_slots_rq91_differential.py
"""
import importlib.util
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R9,
                               UC_ARM_REG_R10, UC_ARM_REG_R11, UC_ARM_REG_SP)

REPRO = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32 = 0xFFFFFFFF
NEEDLE = "IMPORTED-GLOBAL"


def _load(name, file):
    spec = importlib.util.spec_from_file_location(name, REPRO / file)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


npa = _load("npa_linker", "npa_const_addr_differential.py")
boot = _load("boot_sweep", "self_contained_boot_sweep_1189_differential.py")

IMPORT_VALUES = [7, 8]  # what wasmtime binds the imports to

IMP_DEF = r"""(module (import "env" "g" (global i32)) (memory 1) (data (i32.const 16) "\01\02\03\04")
  (global $d i32 (i32.const 42)) (global $e (mut i32) (i32.const 0x12345678))
  (func (export "getd") (result i32) global.get 1)
  (func (export "gete") (result i32) global.get 2)
  (func (export "sete") (global.set 2 (i32.const 5)))
  (func (export "ld") (result i32) i32.const 16 i32.load))"""
TWO_IMP = r"""(module (import "env" "g" (global i32)) (import "env" "h" (global i32)) (memory 1)
  (data (i32.const 16) "\01") (global $d i32 (i32.const 42)) (global $e i32 (i32.const 43))
  (func (export "getd") (result i32) global.get 2) (func (export "gete") (result i32) global.get 3)
  (func (export "ld") (result i32) i32.const 16 i32.load8_u))"""
SP_IMP = r"""(module (import "env" "g" (global i32)) (memory 1) (data (i32.const 16) "\01")
  (global $sp (mut i32) (i32.const 4096))
  (func (export "getsp") (result i32) global.get 1))"""
NO_IMP = r"""(module (memory 1) (data (i32.const 16) "\01\02\03\04")
  (global $d i32 (i32.const 42)) (global $e (mut i32) (i32.const 0x12345678))
  (func (export "getd") (result i32) global.get 0) (func (export "gete") (result i32) global.get 1)
  (func (export "sete") (global.set 1 (i32.const 5))) (func (export "ld") (result i32) i32.const 16 i32.load))"""
WIDE = r"""(module (import "env" "g" (global i32)) (memory 1)
  (global $w (mut i64) (i64.const 0x1122334455667788)) (global $x i32 (i32.const 42))
  (func (export "lo") (result i32) global.get 1 i32.wrap_i64)
  (func (export "hi") (result i32) global.get 1 i64.const 32 i64.shr_u i32.wrap_i64)
  (func (export "getx") (result i32) global.get 2))"""
READS_IMPORT = r"""(module (import "env" "g" (global i32)) (memory 1)
  (func (export "geti") (result i32) global.get 0))"""
UNREFERENCED = r"""(module (import "env" "g" (global i32)) (memory 1)
  (func (export "one") (result i32) i32.const 1))"""

NPA_FLAGS = ["--target", "cortex-m3", "--all-exports", "--relocatable", "--native-pointer-abi"]
SELF_FLAGS = ["--target", "cortex-m4", "--all-exports"]
RELOC_FLAGS = ["--target", "cortex-m4", "--all-exports", "--relocatable",
               "--embedder-global-init", "--embedder-data-init"]

TMP = Path(tempfile.mkdtemp(prefix="impglobal_rq91_"))
fails, compared = [], 0


def reference(wat):
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    m = wasmtime.Module(eng, wat)
    imps = [wasmtime.Global(st, wasmtime.GlobalType(wasmtime.ValType.i32(), False),
                            wasmtime.Val.i32(IMPORT_VALUES[i])) for i, _ in enumerate(m.imports)]
    inst = wasmtime.Instance(st, m, imps)
    return lambda fn: inst.exports(st)[fn](st)


def compile_(label, wat, flags):
    src = TMP / f"{label}.wat"
    src.write_text(wat)
    out = TMP / f"{label}.o"
    if out.exists():
        out.unlink()
    r = subprocess.run([SYNTH, "compile", str(src), "-o", str(out), *flags],
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr, out


def check(leg, label, fn, got, want):
    global compared
    compared += 1
    ok = got == want
    print(f"  [{leg}] {label:8} {fn:6} synth={got} wasmtime={want} {'ok' if ok else 'WRONG'}")
    if not ok:
        fails.append(f"{leg}/{label}/{fn}: synth {got} != wasmtime {want}")


def compiled_or_fail(leg, label, wat, flags):
    rc, log, out = compile_(f"{leg}_{label}", wat, flags)
    if rc != 0:
        fails.append(f"{leg}/{label}: compile must succeed, rc={rc}: {log.strip()[-300:]}")
        return None
    return out


def leg_npa():
    # No `ld` rows here: a low constant address under the native-pointer ABI
    # is the separately pinned #1568 class (npa_const_addr_differential.py).
    for label, wat, seq in (("imp_def", IMP_DEF, ["getd", "gete", "sete", "gete"]),
                            ("two_imp", TWO_IMP, ["getd", "gete"]),
                            ("no_imp", NO_IMP, ["getd", "gete", "sete", "gete"])):
        out = compiled_or_fail("npa", label, wat, NPA_FLAGS)
        if out is None:
            continue
        ref, linked = reference(wat), npa.Linked(out)
        for fn in seq:
            want = ref(fn)
            got = linked.call(fn)
            if want is None:  # a setter: execute it, compare via the next getter
                continue
            check("npa", label, fn, got if isinstance(got, str) else got[0] & M32, want & M32)
    # The stack-pointer global: under the native-pointer ABI its READ is
    # rebased to a native pointer, `__synth_wasm_data + init`.
    out = compiled_or_fail("npa", "sp_imp", SP_IMP, NPA_FLAGS)
    if out is not None:
        linked = npa.Linked(out)
        base, val = linked.syms["__synth_wasm_data"]
        got = linked.call("getsp")
        want = (base + val + reference(SP_IMP)("getsp")) & M32
        check("npa", "sp_imp", "getsp", got if isinstance(got, str) else got[0] & M32, want)


def leg_self():
    for label, wat, seq in (("imp_def", IMP_DEF, ["getd", "gete", "sete", "gete", "ld"]),
                            ("two_imp", TWO_IMP, ["getd", "gete", "ld"]),
                            ("wide", WIDE, ["lo", "hi", "getx"]),
                            ("no_imp", NO_IMP, ["getd", "gete", "sete", "gete", "ld"])):
        out = compiled_or_fail("self", label, wat, SELF_FLAGS)
        if out is None:
            continue
        ref, img = reference(wat), boot.Image(out)
        if img.boot != "ok":
            fails.append(f"self/{label}: boot {img.boot}")
            continue
        snap_after = None
        for fn in seq:
            want = ref(fn)
            if snap_after is not None:  # keep state across a setter
                img.snap = snap_after
            res, _ = img.call(fn, [], 1)
            snap_after = bytes(img.mu.mem_read(img.ram_lo, img.ram_hi - img.ram_lo))
            if want is None:
                continue
            got = res[1][0] if res[0] == "ok" else res[0]
            check("self", label, fn, got, want & M32)


class Embedder:
    """Plain `--relocatable`: the harness plays the embedder of
    docs/embedder-abi-relocatable-arm.md — R9 = globals table seeded with each
    global's init at its slot offset (dense widths, full index space, imports
    first), R11 = linear memory with the data segments applied, R10 = size."""
    TEXT, TABLE, LINMEM, STACK, RET = 0x10000, 0x30000, 0x40000, 0x80000, 0x90000

    def __init__(self, obj, imported_widths, defined):
        e = ELFFile(open(obj, "rb"))
        self.syms = {s.name: s["st_value"] for s in e.get_section_by_name(".symtab").iter_symbols()
                     if s.name and s["st_info"]["type"] == "STT_FUNC"}
        if e.get_section_by_name(".rel.text") is not None:
            sys.exit("reloc leg fixtures must carry no relocation")
        self.mu = mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for b in (self.TEXT, self.TABLE, self.LINMEM, self.STACK - 0x10000, self.RET):
            mu.mem_map(b, 0x10000)
        mu.mem_write(self.TEXT, e.get_section_by_name(".text").data())
        table, off = bytearray(), 0
        for w in imported_widths:  # imported slots: never read (refused)
            table += bytes(w)
        for width, init in defined:
            table += init.to_bytes(width, "little", signed=init < 0)
        mu.mem_write(self.TABLE, bytes(table))
        mu.mem_write(self.RET, b"\x00\xbf\x00\xbf")

    def call(self, fn):
        mu = self.mu
        mu.reg_write(UC_ARM_REG_R9, self.TABLE)
        mu.reg_write(UC_ARM_REG_R10, 0x10000)
        mu.reg_write(UC_ARM_REG_R11, self.LINMEM)
        mu.reg_write(UC_ARM_REG_SP, self.STACK - 0x100)
        mu.reg_write(UC_ARM_REG_LR, self.RET | 1)
        try:
            mu.emu_start((self.TEXT + self.syms[fn]) | 1, self.RET, count=100_000)
        except UcError as ex:
            return f"fault:{ex}"
        return mu.reg_read(UC_ARM_REG_R0) & M32


def leg_reloc():
    for label, wat, imported, defined, seq in (
            ("imp_def", IMP_DEF, [4], [(4, 42), (4, 0x12345678)], ["getd", "gete", "sete", "gete"]),
            ("wide", WIDE, [4], [(8, 0x1122334455667788), (4, 42)], ["lo", "hi", "getx"]),
            ("no_imp", NO_IMP, [], [(4, 42), (4, 0x12345678)], ["getd", "gete", "sete", "gete"])):
        out = compiled_or_fail("reloc", label, wat, RELOC_FLAGS)
        if out is None:
            continue
        ref, emb = reference(wat), Embedder(out, imported, defined)
        for fn in seq:
            want = ref(fn)
            got = emb.call(fn)
            if want is not None:
                check("reloc", label, fn, got, want & M32)


def leg_refuse():
    global compared
    for leg, flags in (("npa", NPA_FLAGS), ("self", SELF_FLAGS), ("reloc", RELOC_FLAGS),
                       ("single", ["--target", "cortex-m4", "--func-name", "geti"])):
        rc, log, out = compile_(f"refuse_{leg}", READS_IMPORT, flags)
        compared += 1
        if rc == 0 or NEEDLE not in log or out.exists():
            fails.append(f"refuse/{leg}: a function reading an imported global must be "
                         f"refused with {NEEDLE} and no object (rc={rc}, object={out.exists()})")
        else:
            print(f"  [refuse] {leg:8} refused with {NEEDLE}")
        rc, log, _ = compile_(f"unref_{leg}", UNREFERENCED,
                              [f if f != "geti" else "one" for f in flags])
        compared += 1
        if rc != 0:
            fails.append(f"unreferenced/{leg}: an unreferenced import must compile: {log[-300:]}")
        else:
            print(f"  [unref]  {leg:8} unreferenced import compiles")


def main():
    print("RQ-91-IMPGLOBAL imported-global slot differential")
    leg_npa()
    leg_self()
    leg_reloc()
    leg_refuse()
    print(f"RQ-91-IMPGLOBAL: {compared} checks, {len(fails)} failure(s)")
    for f in fails:
        print(f"  FAIL {f}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
