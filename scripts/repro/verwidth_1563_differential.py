#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 25
"""#1563 execution differential: the objects VCR-VER-003 newly ACCEPTS run
correctly.

#1563 narrowed the static-data addressing validator (VCR-VER-003,
`synth_core::static_data_addr`) from "every reloc may be an 8-byte access" to
"span each reloc at the access width the ARM backend PROVES from the final
instruction stream". A narrowed safety check owes execution evidence that what
it now lets through is correct, not just that it compiles. This oracle compiles
each newly accepted shape on the native-pointer mixed split
(`--relocatable --native-pointer-abi`), links the object by hand (every
R_ARM_ABS32 / R_ARM_THM_CALL resolved, `.text` / `.data` / `.bss` at SEPARATE
bases so a wrong retargeting cannot land on the right byte by accident) and
runs it under unicorn (Thumb-2, R11 = 0 native deref) against wasmtime on the
same wat, call sequence by call sequence in ONE instance each — so a store
through a narrowed reloc is observed by the loads after it.

Shapes (each was REFUSED by the pre-#1563 validator — measured — and is
compiled clean after it):

  gale_guard  — gale's meld-fused composite reduced to its shape: a Rust
                constructor guard, `i32.load8_u` / `i32.store8` at linmem
                0xe0c, in a 1-byte segment DECLARED AFTER the segment that
                immediately follows it in linear memory (0xe10). The store
                path passes a `bl` before its address register is restored.
                The neighbour's bytes must be untouched by the guard store.
  staggered   — seg_1 overwrites bytes +2,+3 of seg_0. 1-byte loads/stores
                that stay inside the bytes their owner really holds.

NOT here: `scripts/repro/multi_segment_static_data.wat` is also refused
before #1563 and accepted after it on `--native-pointer-abi`. Five of its
exports read wrong bytes on the #1563 change ALONE — not the narrowing: the
module has no stack-pointer global, so const addresses above 0xFFF were baked
as an un-relocated `[r11, rX]`. That root defect is fixed separately (the i32
const-address fold relocates any static address; the arms that cannot fold
refuse) and the module is executed by `npa_const_addr_differential.py`.

It also asserts the compile is now CLEAN (no VCR-VER-003 line), so a
regression of the narrowing reds here as a compile failure first.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/verwidth_1563_differential.py
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
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
R_ARM_ABS32 = 2
R_ARM_THM_CALL = 10
BASES = {".text": 0x10000, ".data": 0x60000, ".bss": 0x80000}
MAPSZ = 0x20000

GALE_GUARD = r"""(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 3600) "\01\02\03\04\05\06\07\08")
  (data (i32.const 3596) "\00")
  (global $calls (mut i32) (i32.const 0))
  (func $ctor
    global.get $calls
    i32.const 1
    i32.add
    global.set $calls)
  (func (export "start")
    i32.const 0
    i32.load8_u offset=3596
    i32.eqz
    if
      i32.const 0
      i32.const 1
      i32.store8 offset=3596
      call $ctor
    end)
  (func (export "guard") (result i32)
    i32.const 0
    i32.load8_u offset=3596)
  (func (export "ctor_calls") (result i32)
    global.get $calls)
  (func (export "nb_lo") (result i32)
    i32.const 0
    i32.load offset=3600)
  (func (export "nb_hi") (result i32)
    i32.const 0
    i32.load offset=3604))"""

STAGGERED = r"""(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 2048) "\a0\a1\a2\a3\a4\a5\a6\a7")
  (data (i32.const 2050) "\b2\b3")
  (func (export "l8u_0") (result i32) i32.const 0 i32.load8_u offset=2048)
  (func (export "l8s_1") (result i32) i32.const 0 i32.load8_s offset=2049)
  (func (export "l8u_2") (result i32) i32.const 0 i32.load8_u offset=2050)
  (func (export "l8u_3") (result i32) i32.const 0 i32.load8_u offset=2051)
  (func (export "l8u_4") (result i32) i32.const 0 i32.load8_u offset=2052)
  (func (export "s8_1") i32.const 0 i32.const 0x5a i32.store8 offset=2049)
  (func (export "s8_2") i32.const 0 i32.const 0x6b i32.store8 offset=2050))"""

# (label, wat text, call sequence). One instance per label on both sides.
CASES = [
    (
        "gale_guard",
        GALE_GUARD,
        ["guard", "nb_lo", "nb_hi", "ctor_calls", "start", "guard", "ctor_calls",
         "nb_lo", "nb_hi", "start", "ctor_calls", "guard"],
    ),
    (
        "staggered",
        STAGGERED,
        ["l8u_0", "l8s_1", "l8u_2", "l8u_3", "l8u_4", "s8_1", "l8s_1", "l8u_0",
         "l8u_2", "s8_2", "l8u_2", "l8u_3", "l8s_1"],
    ),
]


def compile_obj(wat_text, tmp, label):
    src = tmp / f"{label}.wat"
    src.write_text(wat_text)
    obj = tmp / f"{label}.o"
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m3",
         "--all-exports", "--relocatable", "--native-pointer-abi"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    log = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0 or "VCR-VER-003" in log:
        sys.exit(f"{label}: compile must be CLEAN on the mixed split (#1563): "
                 f"rc={r.returncode}\n{log[-1500:]}")
    return obj


def thm_bl(src, dst):
    """Encode a Thumb-2 BL from `src` (the instruction address) to `dst`."""
    off = dst - (src + 4)
    if not -(1 << 24) <= off < (1 << 24):
        sys.exit(f"BL out of range: {off:#x}")
    imm = (off >> 1) & 0xFFFFFF
    s = (imm >> 23) & 1
    i1 = (imm >> 22) & 1
    i2 = (imm >> 21) & 1
    j1 = (~(i1 ^ s)) & 1
    j2 = (~(i2 ^ s)) & 1
    hw1 = 0xF000 | (s << 10) | ((imm >> 11) & 0x3FF)
    hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | (imm & 0x7FF)
    return struct.pack("<HH", hw1, hw2)


class Linked:
    def __init__(self, obj):
        e = ELFFile(open(obj, "rb"))
        secs = list(e.iter_sections())
        names = {i: s.name for i, s in enumerate(secs)}
        self.text = bytearray(e.get_section_by_name(".text").data())
        data = e.get_section_by_name(".data")
        self.data = bytes(data.data()) if data is not None else b""
        bss = e.get_section_by_name(".bss")
        self.bss_size = bss["sh_size"] if bss is not None else 0
        for name, size in ((".text", len(self.text)), (".data", len(self.data)),
                           (".bss", self.bss_size)):
            if size > MAPSZ - 0x200:
                sys.exit(f"{name} is {size} B — larger than the harness map")
        symtab = [s for s in secs if s["sh_type"] == "SHT_SYMTAB"][0]
        self.syms = {}
        for s in symtab.iter_symbols():
            if s.name and s["st_shndx"] not in ("SHN_UNDEF", "SHN_ABS"):
                self.syms[s.name] = BASES.get(names[s["st_shndx"]], None), s["st_value"]
        rel = e.get_section_by_name(".rel.text")
        self.abs32 = 0
        for r in rel.iter_relocations() if rel is not None else []:
            sym = symtab.get_symbol(r["r_info_sym"])
            if sym.name not in self.syms or self.syms[sym.name][0] is None:
                sys.exit(f"unresolvable reloc target {sym.name!r}")
            base, val = self.syms[sym.name]
            where = r["r_offset"]
            if r["r_info_type"] == R_ARM_ABS32:
                (add,) = struct.unpack_from("<I", self.text, where)
                struct.pack_into("<I", self.text, where, (base + val + add) & 0xFFFFFFFF)
                self.abs32 += 1
            elif r["r_info_type"] == R_ARM_THM_CALL:
                dst = (base + val) & ~1
                self.text[where:where + 4] = thm_bl(BASES[".text"] + where, dst)
            else:
                sys.exit(f"unhandled reloc type {r['r_info_type']} for {sym.name}")
        if self.abs32 == 0:
            sys.exit("VACUOUS: no R_ARM_ABS32 static-data relocation in the object")
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for base in BASES.values():
            self.mu.mem_map(base, MAPSZ)
        self.mu.mem_write(BASES[".text"], bytes(self.text))
        self.mu.mem_write(BASES[".data"], self.data)
        self.ret = BASES[".text"] + MAPSZ - 0x10
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")

    def call(self, fn):
        if fn not in self.syms:
            return f"ERR:symbol {fn} missing"
        base, val = self.syms[fn]
        self.mu.reg_write(UC_ARM_REG_R11, 0)  # native deref
        self.mu.reg_write(UC_ARM_REG_SP, BASES[".bss"] + MAPSZ - 0x100)
        self.mu.reg_write(UC_ARM_REG_LR, self.ret | 1)
        try:
            self.mu.emu_start((base + val) | 1, self.ret, timeout=5_000_000)
        except UcError as ex:
            return f"ERR:{ex}"
        lo = self.mu.reg_read(UC_ARM_REG_R0)
        hi = self.mu.reg_read(UC_ARM_REG_R1)
        return lo, hi


def main():
    tmp = Path(tempfile.mkdtemp(prefix="verwidth1563_"))
    fails = 0
    compared = 0
    for label, wat, seq in CASES:
        obj = compile_obj(wat, tmp, label)
        linked = Linked(obj)
        engine = wasmtime.Engine()
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
        print(f"=== {label} ({linked.abs32} static-data ABS32 relocs) ===")
        for fn in seq:
            func = inst.exports(store)[fn]
            res = func(store)
            ntype = func.type(store).results
            got = linked.call(fn)
            if isinstance(got, str):
                ok, shown = False, got
            elif not ntype:
                ok, shown, res = True, "(void)", None
            elif str(ntype[0]) == "i64":
                v = got[0] | (got[1] << 32)
                ok, shown = v == res & 0xFFFFFFFFFFFFFFFF, hex(v)
            else:
                ok, shown = got[0] == res & 0xFFFFFFFF, hex(got[0])
            compared += 1
            fails += not ok
            exp = "(void)" if res is None else hex(res & 0xFFFFFFFFFFFFFFFF)
            print(f"  [{'ok ' if ok else 'BUG'}] {fn}() -> {shown}  (wasmtime {exp})")
    if compared == 0:
        print("VACUOUS: compared nothing")
        return 1
    print(f"\ncompared: {compared}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
