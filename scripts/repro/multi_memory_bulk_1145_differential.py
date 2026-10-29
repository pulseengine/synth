#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 72
"""RQ-89-MEMLAYER6 (#1145) — multi-memory BULK memory on ARM `--relocatable`:
`memory.copy dst_mem src_mem` (0->k, k->0, k->k, j->k) and `memory.fill` on
memory k, with AND without `--native-pointer-abi` — execution differential vs
wasmtime with a per-FUNCTION isolation check.

WHY. `meld --memory multi` lowers a Component Model boundary between two
memory domains as `memory.copy` across memories (`crosses_memory: true`,
measured by gale on #1145). Before this lane the decoder marked every
cross-/non-default-memory `memory.copy` / `memory.fill` unsupported, so the
adapter function was loud-skipped and the compile exited rc 1 (#952). RED at
7e170d62 and at the MEMLAYER6 head before this change: every fixture below
fails at the compile step.

THE LOWERING. Each side of the op resolves against ITS OWN memory: memory 0
is `R11 + addr` (R11 = 0 under `--native-pointer-abi`, so a native pointer;
the embedder's memory-0 base otherwise), memory k is
`__synth_wasm_data_<k> + addr`. The byte loop runs over the ABSOLUTE
pointers, choosing its direction on them, so a same-memory copy is
memmove-correct and a cross-memory copy is correct either way. Inline bounds
checking (`--safety-bounds software|mask`) still refuses any memory-k op —
memory k has no size register — so this oracle runs the unguarded
configurations the downstream uses.

HARNESS. Every section is hand-linked at its own, NON-ADJACENT base with the
gaps unmapped; each access is hooked with its PC and attributed to the
function whose symbol range contains that PC. Every fixture declares, per
function, which memories it may touch: in the adapter fixture ONLY the
adapter — whose body is the two `memory.copy`s and a call — may touch both;
the tenant may touch only memory 0 and the supervisor only memory 1. Result
AND every memory's full contents are compared against wasmtime after each
call. Caller-saved registers and the stack hold garbage.
  npa    `--relocatable --native-pointer-abi`: R11 = 0, memory 0 is the
         `__synth_wasm_data` reservation (+ retargeted `.data` segments);
         a memory-0 pointer argument is passed NATIVE.
  plain  `--relocatable --embedder-data-init --embedder-global-init`: the
         harness is the embedder — memory 0 at R11, R10 = its size, its
         active segments and the R9 globals table written by the harness.

FIXTURES.
  adapter  tenant memory 0 (one __stack_pointer) + supervisor memory 1 (a
           bump-allocator global): the tenant passes a static buffer and a
           shadow-stack result buffer to an adapter that allocates in memory 1,
           copies the argument 0->1, calls the supervisor's in-place
           transform, and copies the result 1->0; plus memory.fill on memory 1,
           an overlapping memory-1 copy in both directions, and the 0->1 /
           1->0 copies with host-supplied addresses.
  bulk3    three memories: 1->0, 0->1, 2->1 (j->k), 1->2, overlapping 1->1 and
           2->2 both ways, zero-length copies at the end of a memory, and
           memory.fill on memories 1 and 2.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/multi_memory_bulk_1145_differential.py
Exits nonzero on any mismatch, isolation breach, compile failure or vacuity.
"""

import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (UC_ARCH_ARM, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE,
                     UC_MODE_THUMB, Uc, UcError)
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
MODES = {
    "npa": ["--native-pointer-abi"],
    "plain": ["--embedder-data-init", "--embedder-global-init"],
}

ADAPTER = r"""(module
  (memory $m0 1 1)
  (memory $m1 1 1)
  (global $sp (mut i32) (i32.const 0x800))
  (global $heap1 (mut i32) (i32.const 0x4000))
  (data (memory $m0) (i32.const 0x1000) "\68\65\6c\6c\6f\2c\20\74\65\6e\61\6e\74\21\21\21")
  (data (memory $m1) (i32.const 0x100) "\01\02\03\04\05\06\07\08")
  (func $s_realloc (param $n i32) (result i32) (local $p i32)
    (local.set $p (global.get $heap1))
    (global.set $heap1 (i32.add (local.get $p) (local.get $n)))
    (local.get $p))
  (func $s_transform (param $p i32) (param $n i32) (local $i i32)
    (block $done (loop $l
      (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
      (i32.store8 $m1 (i32.add (local.get $p) (local.get $i))
        (i32.add (i32.load8_u $m1 (i32.add (local.get $p) (local.get $i))) (i32.const 1)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l))))
  (func $adapter (param $src i32) (param $n i32) (param $out i32) (local $p i32)
    (local.set $p (call $s_realloc (local.get $n)))
    (memory.copy $m1 $m0 (local.get $p) (local.get $src) (local.get $n))
    (call $s_transform (local.get $p) (local.get $n))
    (memory.copy $m0 $m1 (local.get $out) (local.get $p) (local.get $n)))
  (func $tenant_call (export "tenant_call") (result i32) (local $fp i32) (local $r i32)
    (local.set $fp (i32.sub (global.get $sp) (i32.const 32)))
    (global.set $sp (local.get $fp))
    (call $adapter (i32.const 0x1000) (i32.const 16) (local.get $fp))
    (local.set $r (i32.xor (i32.load $m0 (local.get $fp))
                           (i32.load $m0 offset=12 (local.get $fp))))
    (global.set $sp (i32.add (local.get $fp) (i32.const 32)))
    (local.get $r))
  (func $fill1 (export "fill1") (param $d i32) (param $v i32) (param $n i32)
    (memory.fill $m1 (local.get $d) (local.get $v) (local.get $n)))
  (func $copy11 (export "copy11") (param $d i32) (param $s i32) (param $n i32)
    (memory.copy $m1 $m1 (local.get $d) (local.get $s) (local.get $n)))
  (func $copy10 (export "copy10") (param $d i32) (param $s i32) (param $n i32)
    (memory.copy $m1 $m0 (local.get $d) (local.get $s) (local.get $n)))
  (func $copy01 (export "copy01") (param $d i32) (param $s i32) (param $n i32)
    (memory.copy $m0 $m1 (local.get $d) (local.get $s) (local.get $n)))
  (func $peek1 (export "peek1") (param i32) (result i32) (i32.load $m1 (local.get 0)))
  (func $copy_static (export "copy_static")
    (memory.copy $m1 $m0 (i32.const 0x5000) (i32.const 0x1004) (i32.const 8)))
)"""
# function -> memories it may touch. Only the adapter may touch both.
# Internal functions carry only their `func_N` symbol: $s_realloc = func_0,
# $s_transform = func_1, $adapter = func_2.
ADAPTER_FUNCS = {"func_0": set(), "func_1": {1}, "func_2": {0, 1},
                 "tenant_call": {0}, "fill1": {1}, "copy11": {1},
                 "copy10": {0, 1}, "copy01": {0, 1}, "peek1": {1},
                 "copy_static": {0, 1}}
# (export, args). `n:` = a memory-0 pointer (native under npa).
ADAPTER_CALLS = [
    ("tenant_call", []), ("peek1", [0x4000]), ("peek1", [0x400c]),
    ("tenant_call", []), ("peek1", [0x4010]),
    ("fill1", [0x200, 0x1A5, 40]), ("peek1", [0x224]),
    ("copy11", [0x104, 0x100, 8]), ("peek1", [0x108]),
    ("copy11", [0x100, 0x104, 8]), ("peek1", [0x100]),
    ("copy10", [0x6000, "n:0x1000", 16]), ("peek1", [0x6004]),
    ("copy01", ["n:0x700", 0x6000, 12]),
    ("copy10", [0xFFF0, "n:0x1000", 16]), ("copy01", ["n:0x10000", 0x100, 0]),
    # a memory-0 STATIC as a positional cross-copy source (relocated under
    # --native-pointer-abi by the stack-pointer window rule)
    ("copy_static", []), ("peek1", [0x5004]),
]

BULK3 = r"""(module
  (memory $m0 1 1)
  (memory $m1 1 1)
  (memory $m2 1 1)
  (data (memory $m1) (i32.const 0x10) "\10\11\12\13\14\15\16\17\18\19\1a\1b\1c\1d\1e\1f")
  (data (memory $m2) (i32.const 0x20) "\20\21\22\23\24\25\26\27\28\29\2a\2b\2c\2d\2e\2f")
  (func $c10 (export "c10") (param i32 i32 i32) (memory.copy $m1 $m0 (local.get 0) (local.get 1) (local.get 2)))
  (func $c01 (export "c01") (param i32 i32 i32) (memory.copy $m0 $m1 (local.get 0) (local.get 1) (local.get 2)))
  (func $c21 (export "c21") (param i32 i32 i32) (memory.copy $m2 $m1 (local.get 0) (local.get 1) (local.get 2)))
  (func $c12 (export "c12") (param i32 i32 i32) (memory.copy $m1 $m2 (local.get 0) (local.get 1) (local.get 2)))
  (func $c22 (export "c22") (param i32 i32 i32) (memory.copy $m2 $m2 (local.get 0) (local.get 1) (local.get 2)))
  (func $f1 (export "f1") (param i32 i32 i32) (memory.fill $m1 (local.get 0) (local.get 1) (local.get 2)))
  (func $f2 (export "f2") (param i32 i32 i32) (memory.fill $m2 (local.get 0) (local.get 1) (local.get 2)))
  (func $p0 (export "p0") (param i32) (result i32) (i32.load $m0 (local.get 0)))
  (func $p1 (export "p1") (param i32) (result i32) (i32.load $m1 (local.get 0)))
  (func $p2 (export "p2") (param i32) (result i32) (i32.load $m2 (local.get 0)))
)"""
BULK3_FUNCS = {"c10": {0, 1}, "c01": {0, 1}, "c21": {1, 2}, "c12": {1, 2},
               "c22": {2}, "f1": {1}, "f2": {2}, "p0": {0}, "p1": {1}, "p2": {2}}
BULK3_CALLS = [
    ("c01", ["n:0x40", 0x10, 16]), ("p0", ["n:0x44"]),
    ("c10", [0x80, "n:0x40", 16]), ("p1", [0x8c]),
    ("c21", [0x100, 0x10, 16]), ("p2", [0x104]),
    ("c12", [0x200, 0x20, 16]), ("p1", [0x20c]),
    ("c22", [0x24, 0x20, 12]), ("p2", [0x28]),
    ("c22", [0x20, 0x24, 12]), ("p2", [0x20]),
    ("f1", [0x300, 0x77, 33]), ("p1", [0x31c]),
    ("f2", [0xFFFC, 0x99, 4]), ("p2", [0xFFFC]),
    ("c21", [0x10000, 0x10, 0]), ("c01", ["n:0x10000", 0x0, 0]),
]

FIXTURES = [
    ("adapter", ADAPTER, ADAPTER_FUNCS, ADAPTER_CALLS),
    ("bulk3", BULK3, BULK3_FUNCS, BULK3_CALLS),
]


def wat_bytes(lit):
    """Decode a WAT string literal body (`\\hh` escapes and plain chars)."""
    out, i = bytearray(), 0
    while i < len(lit):
        if lit[i] == "\\":
            out.append(int(lit[i + 1:i + 3], 16))
            i += 3
        else:
            out.append(ord(lit[i]))
            i += 1
    return bytes(out)


def segments(wat, mem):
    return [(int(m.group(1), 16), wat_bytes(m.group(2))) for m in re.finditer(
        r'\(data \(memory \$m' + str(mem) + r'\) \(i32\.const (0x[0-9a-f]+)\) "([^"]*)"\)', wat)]


def global_inits(wat):
    return [int(m.group(1), 16) for m in re.finditer(
        r"\(global \$\w+ \(mut i32\) \(i32\.const (0x[0-9a-f]+)\)\)", wat)]


def compile_obj(wat, tmp, label, mode):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}.{mode}.o"
    if obj.exists():
        obj.unlink()
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m3",
         "--all-exports", "--relocatable", *MODES[mode]],
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
    def __init__(self, obj, mode, wat, nmem):
        self.mode = mode
        e = ELFFile(open(obj, "rb"))
        secs = list(e.iter_sections())
        self.sizes, blobs = {}, {}
        for s in secs:
            if s.name in BASES:
                self.sizes[s.name] = s["sh_size"]
                blobs[s.name] = b"" if s["sh_type"] == "SHT_NOBITS" else bytes(s.data())
        symtab = [s for s in secs if s["sh_type"] == "SHT_SYMTAB"][0]
        self.syms, self.abs, self.funcs = {}, {}, []
        for s in symtab.iter_symbols():
            if not s.name:
                continue
            if s["st_shndx"] == "SHN_ABS":
                self.abs[s.name] = s["st_value"]
            elif s["st_shndx"] != "SHN_UNDEF":
                sec = secs[s["st_shndx"]].name
                if sec in BASES:
                    self.syms[s.name] = (sec, s["st_value"], s["st_size"])
                    if sec == ".text" and s["st_size"] and s["st_info"]["type"] == "STT_FUNC":
                        lo = BASES[".text"] + (s["st_value"] & ~1)
                        self.funcs.append((lo, lo + s["st_size"], s.name))
        self.mem0_size = self.abs["__synth_mem_size_0"]
        if mode == "plain" or ".bss" not in self.sizes:
            self.sizes[".bss"] = self.mem0_size
            blobs[".bss"] = b""
            self.syms["__synth_wasm_data"] = (".bss", 0, 0)
        text = bytearray(blobs[".text"])
        for r in e.get_section_by_name(".rel.text").iter_relocations():
            sym = symtab.get_symbol(r["r_info_sym"])
            if sym.name not in self.syms:
                sys.exit(f"unresolvable reloc target {sym.name!r}")
            dst = self.addr(sym.name)
            if r["r_info_type"] == R_ARM_ABS32:
                (add,) = struct.unpack_from("<I", text, r["r_offset"])
                struct.pack_into("<I", text, r["r_offset"], (dst + add) & 0xFFFFFFFF)
            elif r["r_info_type"] == R_ARM_THM_CALL:
                text[r["r_offset"]:r["r_offset"] + 4] = thm_bl(
                    BASES[".text"] + r["r_offset"], dst & ~1)
            else:
                sys.exit(f"unhandled reloc type {r['r_info_type']} for {sym.name}")
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for name, base in BASES.items():
            self.mu.mem_map(base, rup(self.sizes.get(name, 0) + 0x20))
        self.mu.mem_map(STACK_BASE, STACK_SIZE)
        self.mu.mem_map(GLOBALS_BASE, 0x1000)
        self.ret = BASES[".text"] + rup(len(text) + 0x20) - 0x10
        self.mu.mem_write(BASES[".text"], bytes(text))
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")
        for name, blob in blobs.items():
            if blob and name != ".text":
                self.mu.mem_write(BASES[name], blob)
        if mode == "plain":
            # The harness is the embedder: memory 0's segments, R9's table.
            for off, b in segments(wat, 0):
                self.mu.mem_write(BASES[".bss"] + off, b)
            for i, v in enumerate(global_inits(wat)):
                self.mu.mem_write(GLOBALS_BASE + 4 * i, struct.pack("<I", v))
        self.segs0 = segments(wat, 0)
        self.seg_syms = sorted(
            (int(n[len("__synth_wasm_seg_"):]), self.addr(n))
            for n in self.syms if n.startswith("__synth_wasm_seg_"))
        self.accesses = []
        self.mu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, self._hook)
        self.nmem = nmem

    def _hook(self, uc, acc, addr, size, val, ud):
        self.accesses.append((uc.reg_read(UC_ARM_REG_PC), addr))

    def addr(self, name):
        sec, val, _ = self.syms[name]
        return BASES[sec] + val

    def mem_of(self, a):
        for name, base in BASES.items():
            if base <= a < base + max(self.sizes.get(name, 0), 1):
                if name == ".text":
                    return "text"
                if name == ".data":
                    g = self.syms.get("__synth_globals")
                    return "globals" if g and a >= self.addr("__synth_globals") else 0
                return 0 if name == ".bss" else int(name.rsplit("_", 1)[1])
        if STACK_BASE <= a < STACK_BASE + STACK_SIZE:
            return "stack"
        if GLOBALS_BASE <= a < GLOBALS_BASE + 0x1000:
            return "globals"
        return f"OUTSIDE@{a:#x}"

    def func_of(self, pc):
        for lo, hi, name in self.funcs:
            if lo <= pc < hi and not name.startswith("func_"):
                return name
        for lo, hi, name in self.funcs:
            if lo <= pc < hi:
                return name
        return f"pc@{pc:#x}"

    def call(self, fn, args):
        sec, val, _ = self.syms[fn]
        base0 = self.addr("__synth_wasm_data")
        regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
        for i, r in enumerate(regs):
            self.mu.reg_write(r, GARBAGE ^ i)
        for i in range(5):  # r4..r8 garbage; r9..r11 are the ABI registers
            self.mu.reg_write(UC_ARM_REG_R4 + i, GARBAGE ^ (0x100 * i))
        for i, a in enumerate(args):
            if isinstance(a, str):
                a = self.native0(int(a[2:], 16))
            self.mu.reg_write(regs[i], a & 0xFFFFFFFF)
        self.mu.reg_write(UC_ARM_REG_R12, GARBAGE)
        self.mu.reg_write(UC_ARM_REG_R9, GLOBALS_BASE if self.mode == "plain" else GARBAGE)
        self.mu.reg_write(UC_ARM_REG_R11, 0 if self.mode == "npa" else BASES[".bss"])
        self.mu.reg_write(UC_ARM_REG_R10, self.mem0_size)
        self.mu.mem_write(STACK_BASE, bytes([0xA5]) * (STACK_SIZE - 0x100))
        self.mu.reg_write(UC_ARM_REG_SP, STACK_BASE + STACK_SIZE - 0x100)
        self.mu.reg_write(UC_ARM_REG_LR, self.ret | 1)
        self.accesses = []
        try:
            self.mu.emu_start((BASES[sec] + val) | 1, self.ret, timeout=10_000_000)
        except UcError as ex:
            return f"FAULT {ex}"
        return self.mu.reg_read(UC_ARM_REG_R0)

    def native0(self, off):
        """The pointer a host passes for memory-0 offset `off`: the offset
        itself on the plain path; under the native-pointer ABI the address
        the object serves that byte from — inside a retargeted init segment
        (later-declared wins, #757) or else the `__synth_wasm_data`
        reservation."""
        if self.mode != "npa":
            return off
        for k2, a in reversed(self.seg_syms):
            soff, b = self.segs0[k2]
            if soff <= off < soff + len(b):
                return a + (off - soff)
        return self.addr("__synth_wasm_data") + off

    def mem_image(self, k, n):
        if k > 0:
            return bytes(self.mu.mem_read(BASES[f".synth.wasm_mem_{k}"], n))
        img = bytearray(self.mu.mem_read(BASES[".bss"], min(n, self.sizes[".bss"])))
        img += bytes(n - len(img))
        if self.mode == "npa":
            for k2, a in self.seg_syms:
                off, b = self.segs0[k2]
                img[off:off + len(b)] = self.mu.mem_read(a, len(b))
        return bytes(img)


def run(label, wat, funcs, calls, mode, tmp):
    rc, log, obj = compile_obj(wat, tmp, label, mode)
    if rc != 0:
        tail = [ln for ln in log.splitlines() if "rror" in ln or "skipping" in ln][:2]
        print(f"[RED] {label}/{mode}: compile rc={rc}: {' | '.join(tail)[:400]}")
        return 0, 1
    nmem = len(re.findall(r"^\s*\(memory \$m\d+ \d", wat, re.M))
    ln = Linked(obj, mode, wat, nmem)
    wat_x = wat
    for k in range(nmem):
        wat_x = wat_x.replace(f"(memory $m{k} ", f"(memory $m{k} (export \"m{k}\") ", 1)
    cfg = wasmtime.Config()
    cfg.wasm_multi_memory = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    ex = wasmtime.Instance(st, wasmtime.Module(eng, wat_x), []).exports(st)
    wm = [ex[f"m{k}"] for k in range(nmem)]
    fails = compared = 0
    for fn, args in calls:
        wargs = [int(a[2:], 16) if isinstance(a, str) else a for a in args]
        try:
            res = ex[fn](st, *wargs)
            exp = None if res is None else res & 0xFFFFFFFF
        except wasmtime.Trap:
            exp = "trap"
        got = ln.call(fn, args)
        ok = (exp == "trap" and isinstance(got, str)) or (
            isinstance(got, int) and (exp is None or got == exp))
        breach = []
        for pc, a in ln.accesses:
            m = ln.mem_of(a)
            f = ln.func_of(pc)
            if isinstance(m, str) and m.startswith("OUTSIDE"):
                breach.append(f"{f}:{m}")
            elif isinstance(m, int) and m not in funcs.get(f, set()):
                breach.append(f"{f}:m{m}")
        sizes = [w.data_len(st) for w in wm]
        same = [ln.mem_image(k, sizes[k]) == bytes(wm[k].read(st, 0, sizes[k]))
                for k in range(nmem)]
        good = ok and not breach and all(same)
        compared += 1
        fails += not good
        shown = got if isinstance(got, str) else hex(got)
        note = "" if good else (
            f"  <-- {'' if ok else 'RESULT '}"
            f"{'ISOLATION ' + ','.join(sorted(set(breach))[:4]) + ' ' if breach else ''}"
            + " ".join(f"MEM{k}" for k in range(nmem) if not same[k]))
        print(f"  [{'ok ' if good else 'BUG'}] {label}/{mode}.{fn}{tuple(args)} -> {shown} "
              f"(wasmtime {exp if exp in (None, 'trap') else hex(exp)}){note}")
    return compared, fails


def main():
    tmp = Path(tempfile.mkdtemp(prefix="mm_bulk_1145_"))
    total = fails = 0
    for label, wat, funcs, calls in FIXTURES:
        for mode in MODES:
            print(f"=== {label} / {mode} ===")
            c, f = run(label, wat, funcs, calls, mode, tmp)
            total += c
            fails += f
    if total < 72:
        print(f"VACUOUS: compared {total} calls")
        return 1
    print(f"\ncompared: {total}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
