#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 28
"""--native-pointer-abi never bakes a constant static address as a raw
linear-memory offset off R11 — execution differential vs wasmtime.

Under `--native-pointer-abi` R11 is 0 (`CompileConfig::linear_memory_bytes`:
"any address beyond it is a runtime host pointer -> `[R11=0 + addr]`"; the
CLI flag doc's "linmem base = 0"), so a wasm static is reachable ONLY through
the `__synth_wasm_data + C` relocation, retargeted to `__synth_wasm_seg_K` on
the mixed split. Before this fix the selector relocated a constant address
only (a) when a stack-pointer global marked the constant a pointer, (b) for a
memarg offset in the static region (also stack-pointer-gated) or (c) through
the i32 const-address fold, which stopped at the 0xFFF imm12 limit. Every
other constant address was emitted as `movw rX,#addr; ldr [fp, rX]` — reading
absolute address `addr`, not the static. A module with NO stack-pointer
global therefore read wrong bytes for every constant address above 0xFFF, and
for every constant address on the i64 / f32 / f64 / memory.fill /
memory.copy arms, silently (measured at the pre-fix binary: 81 of 162 probe
modules wrong, 0 refused for that reason).

The fix extends (c) to any static address the access would otherwise bake,
and REFUSES loudly the arms that cannot fold. This oracle executes the
relocated shapes against wasmtime (hand-linked, .text/.data/.bss at separate
bases, R11 = 0, one instance per case so a store is observed by the loads
after it) and asserts that every non-folding arm is refused with the precise
diagnostic and no object written.

  nosp       — two segments, no stack-pointer global: a folded low load plus
               loads/stores at 0x1004, 0x1007 and `i32.const 0; offset=0x1000`.
  multi_seg  — scripts/repro/multi_segment_static_data.wat on the mixed split
               (its b_after / d_* / gap exports were wrong before the fix).
  sliver     — WITH a stack-pointer global (0x2000): `i32.const 0x1800
               offset=0x1000`, where neither part is a pointer on its own.

NOT covered, and not catchable by a positional rule: a constant address that
reaches the access through a local or arithmetic, and a dynamic access whose
memarg offset is in the static region of a module with no stack-pointer
global. Both still read the wrong address; they are reported, not pinned.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/npa_const_addr_differential.py
Exits nonzero on any mismatch or missing refusal.
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

HERE = Path(__file__).parent
HERE = Path(__file__).parent
NOSP = r"""(module
  (memory (export "mem") 1)
  (data (i32.const 0x100) "\aa\bb\cc\dd")
  (data (i32.const 0x1000) "\11\22\33\44\55\66\77\88")
  (func (export "low") (result i32) (i32.load (i32.const 0x100)))
  (func (export "high") (result i32) (i32.load (i32.const 0x1004)))
  (func (export "high8") (result i32) (i32.load8_u (i32.const 0x1007)))
  (func (export "high_off") (result i32) (i32.load offset=0x1000 (i32.const 0)))
  (func (export "set_high") (i32.store (i32.const 0x1000) (i32.const 0x5a5a5a5a)))
  (func (export "set_high8") (i32.store8 (i32.const 0x1001) (i32.const 0x77))))"""

SLIVER = r"""(module
  (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x2000))
  (data (i32.const 0x2800) "\31\32\33\34\35\36\37\38")
  (func (export "ld") (result i32) i32.const 0x1800 i32.load offset=0x1000)
  (func (export "ld16") (result i32) i32.const 0x1800 i32.load16_s offset=0x1002)
  (func (export "st8") i32.const 0x1800 i32.const 0x99 i32.store8 offset=0x1001)
  (func (export "st") i32.const 0x1800 i32.const 0x01020304 i32.store offset=0x1004))"""

CASES = [
    ("nosp", NOSP, ["low", "high", "high8", "high_off", "set_high", "high",
                    "set_high8", "high8", "low"]),
    ("multi_seg", (HERE / "multi_segment_static_data.wat").read_text(),
     ["a_lo", "a_hi", "b_straddle", "b_after", "c_head", "c_ovl", "d_lo",
      "d_hi", "d_byte", "e_0", "e_16", "e_28", "gap"]),
    ("sliver", SLIVER, ["ld", "ld16", "st8", "ld", "st", "ld16"]),
]

# Arms that cannot fold a constant address: each must be REFUSED. (label,
# target, function body). Every module carries the folded `anchor` so the
# region is referenced and the #1041 refusal cannot be what fires.
REFUSE_HDR = r"""(module (memory (export "mem") 1)
  (data (i32.const 0x100) "\01\02\03\04\05\06\07\08")
  (data (i32.const 0x1000) "\11\12\13\14\15\16\17\18")
  (func (export "anchor") (result i32) (i32.load (i32.const 0x100)))
  (func (export "f") """
REFUSE = [
    ("i64_load", "cortex-m3", "(result i64) i32.const 0x1000 i64.load"),
    ("i64_load_low", "cortex-m3", "(result i64) i32.const 0x100 i64.load"),
    ("i64_store", "cortex-m3", "i32.const 0x1000 i64.const 7 i64.store"),
    ("i64_load8", "cortex-m3", "(result i64) i32.const 0x1001 i64.load8_u"),
    ("f32_store", "cortex-m7dp", "i32.const 0x1000 f32.const 1 f32.store"),
    ("f64_load", "cortex-m7dp", "(result f64) i32.const 0x1000 f64.load"),
    ("memory_fill", "cortex-m3",
     "i32.const 0x1000 i32.const 9 i32.const 4 memory.fill"),
    ("memory_copy_src", "cortex-m3",
     "i32.const 0x104 i32.const 0x1000 i32.const 4 memory.copy"),
]
NEEDLE = "which this lowering would emit as a raw linear-memory offset off R11"


def assert_refusals(tmp):
    n = 0
    for label, tgt, body in REFUSE:
        src = tmp / f"refuse_{label}.wat"
        src.write_text(REFUSE_HDR + body + "))")
        obj = tmp / f"refuse_{label}.o"
        r = subprocess.run(
            [SYNTH, "compile", str(src), "-o", str(obj), "--target", tgt,
             "--all-exports", "--relocatable", "--native-pointer-abi"],
            capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
        )
        log = (r.stdout or "") + (r.stderr or "")
        if r.returncode == 0:
            sys.exit(f"refuse {label}: compiled with exit 0 — a constant static "
                     f"address on a non-folding arm must be refused")
        if "panicked at" in log:
            sys.exit(f"refuse {label}: refusal PANICKED: {log[-400:]}")
        if NEEDLE not in log or "--native-pointer-abi:" not in log:
            sys.exit(f"refuse {label}: refused for the WRONG reason:\n{log[-800:]}")
        if obj.exists() and obj.stat().st_size > 0:
            sys.exit(f"refuse {label}: an object was written despite the refusal")
        print(f"  [ok ] refused: {label}")
        n += 1
    return n


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
        sys.exit(f"{label}: compile must be CLEAN: "
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
    print("=== non-folding arms (must be refused) ===")
    refusals = assert_refusals(tmp)
    # Non-vacuity for the refusal half (#1113): the emulation floor cannot
    # see a refused compile, so it is counted here.
    if refusals != len(REFUSE):
        print(f"VACUOUS: refusals={refusals} of {len(REFUSE)}")
        return 1
    print(f"refusals: {refusals}")
    print(f"\ncompared: {compared}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails} divergences)'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
