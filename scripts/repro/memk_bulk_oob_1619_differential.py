#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 214
"""MEMKBULK (#1619) — an OUT-OF-BOUNDS `memory.fill` / `memory.copy` on a
NON-DEFAULT memory k must trap BEFORE writing any byte, under
`--safety-bounds software`, on ARM `--relocatable` with AND without
`--native-pointer-abi` — execution differential vs wasmtime.

WHY. Since #1605 (v0.89, #1145) `memory.fill` on memory k and `memory.copy`
across memories compile on ARM `--relocatable`, as the unguarded #374 byte
loop. WebAssembly checks the WHOLE range of a bulk op before it writes
anything: an out-of-bounds fill/copy traps and writes NOTHING. synth wrote the
in-bounds bytes AND the bytes past memory k's end, and no configuration could
change that for memory k: `--safety-bounds software|mask` refused every
memory-k op, because their guards read R10, which is MEMORY 0's size.
RED at c20d37b2: every software leg below is refused at compile (rc 1, #952).

THE GUARD. Under `--safety-bounds software` each side of the op is checked
against ITS OWN memory's size before the loop: memory k against
`__synth_mem_size_k` (the SHN_ABS region-table symbol, loaded through an
R_ARM_ABS32 literal — the declared byte size, `(pagesize 1)` included),
memory 0 against R10 exactly as memory 0's own bulk ops are. `dst+len`
overflowing u32, or exceeding the size, traps with an inline UDF; `== size` is
in bounds; `len = 0` traps only past the end. No byte is written before every
check passes.

HARNESS. Every section is hand-linked at its own NON-ADJACENT base. After each
memory's end the harness maps a CANARY band (filled with 0x5A) so a write past
the end lands and is SEEN — a fault into unmapped memory is never mistaken for
a trap. A trap counts ONLY when the emulator stops on an invalid instruction
whose halfword is `UDF #0` (0xDE00); any other stop is a BUG. After every call
the result, EVERY memory's full contents (vs wasmtime) AND every canary band
are compared. The memories have three DIFFERENT sizes — memory 0 = 64 KiB,
memory 1 = 5,376 B `(pagesize 1)` (gale's extent, not a power of two), memory
2 = 128 KiB — so a guard checking the wrong memory's bound is visible: rows
sit between the sizes in both directions.

LEGS.
  software/plain  `--safety-bounds software --embedder-data-init
                  --embedder-global-init` — gated: trap rows must trap.
  software/npa    `--safety-bounds software --native-pointer-abi`. Memory 0
                  pointers are NATIVE; the cross-memory copies with a memory-0
                  side are refused under this pair (the memory-0 guard compares
                  against R10, which has no meaning for a native pointer), so
                  this leg runs the memory-k-only fixture and asserts that
                  refusal.
  none/plain, none/npa  — the documented default envelope (no OOB trap):
                  ONLY the in-bounds rows are executed and must match; the OOB
                  rows are not asserted (synth makes no trap claim there).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/memk_bulk_oob_1619_differential.py
Exits nonzero on any mismatch, canary write, non-UDF fault, compile failure or
vacuity.
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
from unicorn.unicorn_const import UC_ERR_INSN_INVALID
from unicorn.arm_const import (UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0,
                               UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                               UC_ARM_REG_R4, UC_ARM_REG_R9, UC_ARM_REG_R10,
                               UC_ARM_REG_R11, UC_ARM_REG_R12, UC_ARM_REG_SP)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
R_ARM_ABS32 = 2
R_ARM_THM_CALL = 10
BASES = {".text": 0x0010_0000, ".bss": 0x0040_0000, ".data": 0x0080_0000,
         ".synth.wasm_mem_1": 0x0100_0000, ".synth.wasm_mem_2": 0x0180_0000}
GLOBALS_BASE = 0x0300_0000
STACK_BASE, STACK_SIZE = 0x0200_0000, 0x1_0000
GARBAGE = 0xDEADBEEF
CANARY, CANARY_LEN = 0x5A, 0x2000
S0, S1, S2 = 0x10000, 5376, 0x20000

MEMS = (f'(memory $m0 1 1) (memory $m1 {S1} {S1} (pagesize 1)) '
        f'(memory $m2 2 2)')
KFUNCS = r"""
  (func (export "fill1") (param i32 i32 i32) (memory.fill $m1 (local.get 0) (local.get 1) (local.get 2)))
  (func (export "fill2") (param i32 i32 i32) (memory.fill $m2 (local.get 0) (local.get 1) (local.get 2)))
  (func (export "copy11") (param i32 i32 i32) (memory.copy $m1 $m1 (local.get 0) (local.get 1) (local.get 2)))
  (func (export "copy12") (param i32 i32 i32) (memory.copy $m1 $m2 (local.get 0) (local.get 1) (local.get 2)))
  (func (export "copy21") (param i32 i32 i32) (memory.copy $m2 $m1 (local.get 0) (local.get 1) (local.get 2)))
  (func (export "fill1c") (memory.fill $m1 (i32.const 0x1400) (i32.const 0x3C) (i32.const 0x101)))
  (func (export "ld1_32") (param i32) (result i32) (i32.load $m1 offset=4 (local.get 0)))
  (func (export "ld1_8u") (param i32) (result i32) (i32.load8_u $m1 (local.get 0)))
  (func (export "ld1_16s") (param i32) (result i32) (i32.load16_s $m1 offset=16 (local.get 0)))
  (func (export "ld1_64") (param i32) (result i64) (i64.load $m1 offset=8 align=4 (local.get 0)))
  (func (export "ld1_64_32u") (param i32) (result i64) (i64.load32_u $m1 (local.get 0)))
  (func (export "ld1_big") (param i32) (result i32) (i32.load $m1 offset=0x10000 (local.get 0)))
  (func (export "ld2_64") (param i32) (result i64) (i64.load $m2 (local.get 0)))
  (func (export "ld2_big") (param i32) (result i32) (i32.load $m2 offset=0x10000 (local.get 0)))
  (func (export "st1_32") (param i32 i32) (i32.store $m1 offset=4 (local.get 0) (local.get 1)))
  (func (export "st1_8") (param i32 i32) (i32.store8 $m1 (local.get 0) (local.get 1)))
  (func (export "st1_16") (param i32 i32) (i32.store16 $m1 (local.get 0) (local.get 1)))
  (func (export "st1_64") (param i32 i64) (i64.store $m1 offset=8 (local.get 0) (local.get 1)))
  (func (export "st1_64_8") (param i32 i64) (i64.store8 $m1 (local.get 0) (local.get 1)))
  (func (export "st2_64") (param i32 i64) (i64.store $m2 (local.get 0) (local.get 1)))
"""
RES64 = {"ld1_64", "ld1_64_32u", "ld2_64"}
V64 = 0x8000_0001_FFFF_FFFE
XFUNCS = r"""
  (func (export "copy10") (param i32 i32 i32) (memory.copy $m1 $m0 (local.get 0) (local.get 1) (local.get 2)))
  (func (export "copy01") (param i32 i32 i32) (memory.copy $m0 $m1 (local.get 0) (local.get 1) (local.get 2)))
"""
KMOD = f"(module {MEMS} {KFUNCS})"
XMOD = f"(module {MEMS} {KFUNCS} {XFUNCS})"

T = "trap"
# (export, args, in_bounds). `n:` = a memory-0 offset (native under npa).
KCALLS = [
    ("fill1", [0x100, 0xAB, 0x40], 1),            # seeds: no data segments,
    ("fill1", [0x120, 0x81, 0x30], 1),            # so the copies move
    ("fill2", [0x8000, 0xC7, 0x20], 1),           # non-zero bytes
    ("fill2", [0x8008, 0x3D, 0x4], 1),
    ("fill1", [S1 - 0x20, 0xC1, 0x20], 1),        # ends exactly at the size
    ("fill1", [S1, 0x11, 0], 1),                  # len 0 at the size
    ("fill1", [S1 + 1, 0x12, 0], 0),              # len 0 one past the size
    ("fill1", [S1 - 0x10, 0xD2, 0x20], 0),        # straddles the end
    ("fill1", [S1 - 0x20, 0xD3, 0x21], 0),        # one byte too long
    ("fill1", [S1 + 0x10, 0xE3, 4], 0),           # fully past the end
    ("fill1", [0x2000, 0xE4, 4], 0),              # past memory 1, inside S0
    ("fill1", [0xFFFF_FFF0, 0xF4, 0x20], 0),      # dst+len wraps u32
    ("fill1", [0x10, 0xF5, 0xFFFF_FFF8], 0),      # len wraps u32
    ("fill1c", [], 0),                            # the #1619 shape, constants
    ("fill2", [S2 - 4, 0x99, 4], 1),
    ("fill2", [0x18000, 0x97, 0x10], 1),          # past memory 0/1, inside S2
    ("fill2", [S2 - 4, 0x98, 5], 0),
    ("fill2", [S2, 0x96, 0], 1),
    ("copy11", [0x200, 0x100, 0x40], 1),
    ("copy11", [0x104, 0x100, 0x20], 1),          # overlapping, backward
    ("copy11", [0x100, 0x104, 0x20], 1),          # overlapping, forward
    ("copy11", [0x100, S1 - 0x10, 0x20], 0),      # ONLY the source is OOB
    ("copy11", [S1 - 0x10, 0x100, 0x20], 0),      # ONLY the destination
    ("copy11", [S1, S1, 0], 1),
    ("copy11", [S1 + 1, 0x100, 0], 0),
    ("copy11", [0x100, S1 + 1, 0], 0),
    ("copy11", [0x100, 0xFFFF_FFF0, 0x20], 0),    # src+len wraps u32
    ("copy12", [0x300, 0x8000, 0x10], 1),         # src past S1, inside S2
    ("copy12", [0x300, S2 - 8, 0x10], 0),         # source OOB in memory 2
    ("copy12", [S1 - 8, 0x8000, 0x10], 0),        # destination OOB in memory 1
    ("copy21", [0x18000, 0x100, 0x10], 1),        # dst past S0, inside S2
    ("copy21", [0x18000, S1 - 8, 0x10], 0),       # source OOB in memory 1
    ("copy21", [S2 - 8, 0x100, 0x10], 0),         # destination OOB in memory 2
    # plain loads/stores on memory k (an i64 arg is passed in R2:R3, #518)
    ("st1_32", [S1 - 8, 0x1234_5678], 1),         # ends exactly at the size
    ("st1_32", [S1 - 7, 0x2345_6789], 0),
    ("st1_32", [0x2000, 0x3456_789A], 0),         # past memory 1, inside S0
    ("st1_32", [0xFFFF_FFFC, 0x4567_89AB], 0),    # addr+offset wraps u32
    ("st1_8", [S1 - 1, 0x1EE], 1),
    ("st1_8", [S1, 0x1DD], 0),
    ("st1_16", [S1 - 2, 0xBEEF], 1),
    ("st1_16", [S1 - 1, 0xCAFE], 0),
    ("st1_64", [S1 - 16, V64], 1),
    ("st1_64", [S1 - 12, V64 ^ 0xFF], 0),      # low word fits, high does not
    ("st1_64", [S1 - 15, V64 ^ 0xF0F0], 0),
    ("st1_64_8", [S1 - 1, V64], 1),
    ("st1_64_8", [S1, V64], 0),
    ("st2_64", [S2 - 8, V64 ^ 1], 1),
    ("st2_64", [0x18000, V64 ^ 2], 1),         # past memory 0/1, inside S2
    ("st2_64", [S2 - 4, V64 ^ 3], 0),
    ("ld1_32", [S1 - 8], 1),
    ("ld1_32", [S1 - 7], 0),
    ("ld1_32", [0x2000], 0),
    ("ld1_32", [0xFFFF_FFFC], 0),
    ("ld1_8u", [S1 - 1], 1),
    ("ld1_8u", [S1], 0),
    ("ld1_16s", [S1 - 0x12], 1),
    ("ld1_16s", [S1 - 0x11], 0),
    ("ld1_64", [S1 - 16], 1),
    ("ld1_64", [S1 - 15], 0),
    ("ld1_64", [S1 - 12], 0),                     # low word fits, high does not
    ("ld1_64_32u", [S1 - 4], 1),
    ("ld1_64_32u", [S1 - 3], 0),
    ("ld1_big", [0], 0),                          # offset alone exceeds S1
    ("ld2_64", [S2 - 8], 1),
    ("ld2_64", [0x18000], 1),                     # past memory 0/1, inside S2
    ("ld2_64", [S2 - 7], 0),
    ("ld2_big", [S2 - 0x10000 - 4], 1),           # large offset, end-exact
    ("ld2_big", [S2 - 0x10000 - 3], 0),
    ("ld2_big", [0xFFFF_0000], 0),                # addr+offset wraps u32
]
XCALLS = KCALLS + [
    ("copy10", [0x300, "n:0x40", 0x20], 1),
    ("copy10", [0x300, "n:0x8000", 0x10], 1),     # src past S1, inside S0
    ("copy10", [S1 - 8, "n:0x40", 0x10], 0),      # dst OOB in memory 1
    ("copy10", [0x300, f"n:{S0 - 8:#x}", 0x10], 0),  # src OOB in memory 0
    ("copy01", ["n:0x80", 0x100, 0x20], 1),
    ("copy01", ["n:0x9000", 0x100, 0x10], 1),     # dst past S1, inside S0
    ("copy01", [f"n:{S0 - 8:#x}", 0x100, 0x10], 0),  # dst OOB in memory 0
    ("copy01", ["n:0x80", S1 - 8, 0x10], 0),      # src OOB in memory 1
]
LEGS = [
    # (name, flags, module, calls, assert_oob)
    ("software/plain", ["--safety-bounds", "software", "--embedder-data-init",
                        "--embedder-global-init"], XMOD, XCALLS, True),
    ("software/npa", ["--safety-bounds", "software", "--native-pointer-abi"],
     KMOD, KCALLS, True),
    ("none/plain", ["--embedder-data-init", "--embedder-global-init"],
     XMOD, XCALLS, False),
    ("none/npa", ["--native-pointer-abi"], XMOD, XCALLS, False),
]
# The refusal the software/npa leg asserts for a memory-0 side.
NPA_XREFUSAL = "npa-software-bounds (#1661)"
FLOOR = 0  # set below from the leg table; the vacuity floor


def compile_obj(wat, tmp, label, flags):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}.o"
    if obj.exists():
        obj.unlink()
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m3",
         "--all-exports", "--relocatable", *flags],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    return r.returncode, (r.stdout or "") + (r.stderr or ""), obj


def thm_bl(src, dst):
    off = dst - (src + 4)
    imm = (off >> 1) & 0xFFFFFF
    s, i1, i2 = (imm >> 23) & 1, (imm >> 22) & 1, (imm >> 21) & 1
    j1, j2 = (~(i1 ^ s)) & 1, (~(i2 ^ s)) & 1
    return struct.pack("<HH", 0xF000 | (s << 10) | ((imm >> 11) & 0x3FF),
                       0xD000 | (j1 << 13) | (j2 << 11) | (imm & 0x7FF))


def rup(n):
    return max(0x1000, (n + 0xFFF) & ~0xFFF)


class Linked:
    def __init__(self, obj, npa):
        self.npa = npa
        e = ELFFile(open(obj, "rb"))
        secs = list(e.iter_sections())
        self.sizes, blobs = {}, {}
        for s in secs:
            if s.name in BASES:
                self.sizes[s.name] = s["sh_size"]
                blobs[s.name] = b"" if s["sh_type"] == "SHT_NOBITS" else bytes(s.data())
        symtab = [s for s in secs if s["sh_type"] == "SHT_SYMTAB"][0]
        self.syms, self.abs = {}, {}
        for s in symtab.iter_symbols():
            if not s.name:
                continue
            if s["st_shndx"] == "SHN_ABS":
                self.abs[s.name] = s["st_value"]
            elif s["st_shndx"] != "SHN_UNDEF":
                sec = secs[s["st_shndx"]].name
                if sec in BASES:
                    self.syms[s.name] = (sec, s["st_value"])
        self.msize = [self.abs["__synth_mem_size_0"], self.abs["__synth_mem_size_1"],
                      self.abs["__synth_mem_size_2"]]
        if not npa or ".bss" not in self.sizes:
            self.sizes[".bss"] = self.msize[0]
            blobs[".bss"] = b""
            self.syms["__synth_wasm_data"] = (".bss", 0)
        text = bytearray(blobs[".text"])
        self.abs_relocs = 0
        rel = e.get_section_by_name(".rel.text")
        for r in (rel.iter_relocations() if rel else []):
            sym = symtab.get_symbol(r["r_info_sym"])
            if sym["st_shndx"] == "SHN_ABS":
                dst = sym["st_value"]  # an absolute value: resolves to itself
                self.abs_relocs += 1
            elif sym.name in self.syms:
                dst = self.addr(sym.name)
            else:
                sys.exit(f"unresolvable reloc target {sym.name!r}")
            if r["r_info_type"] == R_ARM_ABS32:
                (add,) = struct.unpack_from("<I", text, r["r_offset"])
                struct.pack_into("<I", text, r["r_offset"], (dst + add) & 0xFFFFFFFF)
            elif r["r_info_type"] == R_ARM_THM_CALL:
                text[r["r_offset"]:r["r_offset"] + 4] = thm_bl(
                    BASES[".text"] + r["r_offset"], dst & ~1)
            else:
                sys.exit(f"unhandled reloc type {r['r_info_type']} for {sym.name}")
        self.text = bytes(text)
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for name, base in BASES.items():
            self.mu.mem_map(base, rup(self.sizes.get(name, 0) + CANARY_LEN + 0x20))
        self.mu.mem_map(STACK_BASE, STACK_SIZE)
        self.mu.mem_map(GLOBALS_BASE, 0x1000)
        self.ret = BASES[".text"] + rup(len(text) + CANARY_LEN + 0x20) - 0x10
        self.mu.mem_write(BASES[".text"], self.text)
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")
        for name, blob in blobs.items():
            if blob and name != ".text":
                self.mu.mem_write(BASES[name], blob)
        for k in (0, 1, 2):
            self.mu.mem_write(self.mem_end(k), bytes([CANARY]) * CANARY_LEN)

    def addr(self, name):
        sec, val = self.syms[name]
        return BASES[sec] + val

    def mem_base(self, k):
        return self.addr("__synth_wasm_data") if k == 0 else BASES[f".synth.wasm_mem_{k}"]

    def mem_end(self, k):
        if k == 0:
            return BASES[".bss"] + self.sizes[".bss"]
        return BASES[f".synth.wasm_mem_{k}"] + self.sizes[f".synth.wasm_mem_{k}"]

    def canary_ok(self, k):
        return bytes(self.mu.mem_read(self.mem_end(k), CANARY_LEN)) == bytes([CANARY]) * CANARY_LEN

    def image(self, k):
        return bytes(self.mu.mem_read(self.mem_base(k), self.msize[k]))

    def native0(self, off):
        return self.addr("__synth_wasm_data") + off if self.npa else off

    def call(self, fn, args):
        regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
        for i, r in enumerate(regs):
            self.mu.reg_write(r, GARBAGE ^ i)
        for i in range(5):
            self.mu.reg_write(UC_ARM_REG_R4 + i, GARBAGE ^ (0x100 * i))
        for i, a in enumerate(args):
            if isinstance(a, str):
                a = self.native0(int(a[2:], 16))
            if a > 0xFFFFFFFF:  # an (i32, i64) i64: the even pair R2:R3 (#518)
                self.mu.reg_write(UC_ARM_REG_R2, a & 0xFFFFFFFF)
                self.mu.reg_write(UC_ARM_REG_R3, a >> 32)
                continue
            self.mu.reg_write(regs[i], a & 0xFFFFFFFF)
        self.mu.reg_write(UC_ARM_REG_R12, GARBAGE)
        self.mu.reg_write(UC_ARM_REG_R9, GLOBALS_BASE)
        self.mu.reg_write(UC_ARM_REG_R11, 0 if self.npa else BASES[".bss"])
        self.mu.reg_write(UC_ARM_REG_R10, self.msize[0])
        self.mu.reg_write(UC_ARM_REG_SP, STACK_BASE + STACK_SIZE - 0x100)
        self.mu.reg_write(UC_ARM_REG_LR, self.ret | 1)
        try:
            self.mu.emu_start(self.addr(fn) | 1, self.ret, timeout=20_000_000)
        except UcError as ex:
            pc = self.mu.reg_read(UC_ARM_REG_PC)
            off = (pc & ~1) - BASES[".text"]
            hw = struct.unpack_from("<H", self.text, off)[0] if 0 <= off < len(self.text) - 1 else None
            if ex.errno == UC_ERR_INSN_INVALID and hw == 0xDE00:
                return T
            return f"FAULT {ex} @pc={pc:#x}"
        lo, hi = self.mu.reg_read(UC_ARM_REG_R0), self.mu.reg_read(UC_ARM_REG_R1)
        return ("ret", lo, hi)


def run_leg(name, flags, wat, calls, assert_oob, tmp):
    label = name.replace("/", "_")
    rc, log, obj = compile_obj(wat, tmp, label, flags)
    if rc != 0:
        tail = [ln for ln in log.splitlines() if "rror" in ln or "skipping" in ln][:2]
        print(f"[RED] {name}: compile rc={rc}: {' | '.join(tail)[:400]}")
        return 0, len([c for c in calls if c[2] or assert_oob]) or 1
    ln = Linked(obj, "--native-pointer-abi" in flags)
    if "software" in flags and ln.abs_relocs == 0:
        print(f"[RED] {name}: no R_ARM_ABS32 against an SHN_ABS size symbol — "
              "the memory-k guard is absent")
        return 0, 1
    wat_x = wat
    for k in range(3):
        wat_x = wat_x.replace(f"(memory $m{k} ", f"(memory $m{k} (export \"m{k}\") ", 1)
    cfg = wasmtime.Config()
    cfg.wasm_multi_memory = True
    cfg.wasm_custom_page_sizes = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    ex = wasmtime.Instance(st, wasmtime.Module(eng, wat_x), []).exports(st)
    wm = [ex[f"m{k}"] for k in range(3)]
    if [w.data_len(st) for w in wm] != ln.msize:
        print(f"[RED] {name}: size symbols {ln.msize} != wasmtime "
              f"{[w.data_len(st) for w in wm]}")
        return 0, 1
    compared = fails = 0
    for fn, args, inb in calls:
        if not inb and not assert_oob:
            continue
        wargs = [int(a[2:], 16) if isinstance(a, str) else a for a in args]
        try:
            res = ex[fn](st, *wargs)
            exp = "ret" if res is None else f"ret {res & ((1 << 64) - 1 if fn in RES64 else 0xFFFFFFFF):#x}"
        except wasmtime.Trap:
            exp = T
        got = ln.call(fn, args)
        if isinstance(got, tuple):
            _, lo, hi = got
            got = "ret" if not exp.startswith("ret ") else (
                f"ret {(hi << 32 | lo) if fn in RES64 else lo:#x}")
        if (exp == T) == bool(inb):
            print(f"[RED] {name}: row table wrong — {fn}{tuple(args)} in_bounds={inb} "
                  f"but wasmtime {exp}")
            return compared, fails + 1
        same = [ln.image(k) == bytes(wm[k].read(st, 0, ln.msize[k])) for k in range(3)]
        canary = [ln.canary_ok(k) for k in range(3)]
        good = got == exp and all(same) and all(canary)
        compared += 1
        fails += not good
        note = "" if good else ("  <-- " + ("" if got == exp else "RESULT ")
                                + " ".join(f"MEM{k}" for k in range(3) if not same[k]) + " "
                                + " ".join(f"PAST-END{k}" for k in range(3) if not canary[k]))
        print(f"  [{'ok ' if good else 'BUG'}] {name}.{fn}{tuple(args)} -> {got} "
              f"(wasmtime {exp}){note}")
        if not good:
            # resync: a divergent write would poison every later row
            for k in range(3):
                ln.mu.mem_write(ln.mem_base(k), bytes(wm[k].read(st, 0, ln.msize[k])))
                ln.mu.mem_write(ln.mem_end(k), bytes([CANARY]) * CANARY_LEN)
    return compared, fails


def npa_xcopy_refused(tmp):
    """Under software + native-pointer ABI a cross-memory copy with a memory-0
    side must be REFUSED, loudly — never guarded against R10."""
    bad = 0
    for fn in ("copy10", "copy01"):
        body = [ln for ln in XFUNCS.splitlines() if f'"{fn}"' in ln][0]
        wat = f"(module {MEMS} {body})"
        rc, log, _ = compile_obj(wat, tmp, f"npa_refuse_{fn}",
                                 ["--safety-bounds", "software", "--native-pointer-abi"])
        ok = rc != 0 and NPA_XREFUSAL in log
        bad += not ok
        print(f"  [{'ok ' if ok else 'BUG'}] software/npa refuses {fn}: rc={rc}")
    return bad


def main():
    tmp = Path(tempfile.mkdtemp(prefix="memk_bulk_1619_"))
    total = fails = 0
    measure = os.environ.get("MEMK_MEASURE") == "1"  # record-only: OOB rows on every leg
    for name, flags, wat, calls, assert_oob in LEGS:
        assert_oob = assert_oob or measure
        print(f"=== {name} ===")
        c, f = run_leg(name, flags, wat, calls, assert_oob, tmp)
        total += c
        fails += f
    print("=== software/npa refusals ===")
    fails += npa_xcopy_refused(tmp)
    floor = sum(len([c for c in calls if c[2] or oob]) for _, _, _, calls, oob in LEGS)
    if total < floor:
        print(f"VACUOUS: compared {total} calls, expected {floor}")
        fails += 1
    print(f"\ncompared: {total} (expected {floor})")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
