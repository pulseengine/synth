#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 5388
"""MEMK64 (#1622) — the i64 load/store family on a NON-DEFAULT memory, on ARM
`--relocatable`, with AND without `--native-pointer-abi` — execution
differential vs wasmtime with a per-FUNCTION isolation check.

WHY. gale's two-domain image (`meld fuse --memory shared --pack-rebase
--domain tenant=... --domain supervisor=... --memory-page-size 1`) carries 12
wide accesses on memory 1 in its fused supervisor domain — u64 fields of the
mpu-thin / switch-thin drivers:

    2  i64.load 1 offset=8 align=4      2  i64.store 1 offset=8 align=4
    3  i64.load32_u 1 (offsets 24, 28, 48)
    5  i64.store 1 (offsets 0, 16 x2, 24 x2, 108)

Before this lane the memory-k selector arm refused every non-i32 access ("only
the i32 load/store family is (#406)"), the 4 functions holding them were
loud-skipped, and #1102/#952 refused the object. RED at v0.89.0 (dd2b791a):
every fixture below fails at the compile step.

THE LOWERING. Memory k is `__synth_wasm_data_<k> + offset + addr` — exactly the
i32 family's base — with memory 0's #746 pair forms: `I64Ldr`/`I64Str` are two
word accesses (never LDRD/STRD, so align=4 and byte-unaligned i64 accesses are
correct on Cortex-M3), and a narrow load fills the high word by sign or zero
extension. Narrow stores write the low word only.

HARNESS. Every section is hand-linked at its own NON-ADJACENT base with the
gaps unmapped; each access is hooked and attributed to the function whose
symbol range contains its PC. The load/store functions may touch ONLY memory
1; the two transfer functions may touch both. Memory 1 is SEEDED from a data
segment on memory 1 with distinct bytes (high bits set), so a load reads the
same source bytes in both runtimes and a swapped word, a missing high-word
fill or a wrong extension is visible in the result. After EVERY call the
result (i64 = R1:R0) AND every memory's full contents are compared against
wasmtime byte for byte — a store is never checked by reading it back through
synth. Argument registers, R4-R8, R12 and the stack hold garbage.

AAPCS: an `(i32, i64)` signature passes the i64 in R2:R3 (even-register
alignment, the #518 rule).

FIXTURES x MODES x TARGETS.
  gale   memory 0 = 2,080 B and memory 1 = 5,376 B declared `(pagesize 1)` —
         the meld#530 byte extents gale measured on #1622
  paged  two ordinary one-page (64 KiB) memories
  npa    `--relocatable --native-pointer-abi`
  plain  `--relocatable --embedder-data-init --embedder-global-init`
  cortex-m3 / cortex-m4f / cortex-m7

Every load width at gale's offsets (0, 8, 16, 24, 28, 48, 108), i64.load and
i64.store at align=4 AND natural alignment, at word-aligned, byte-unaligned and
end-of-memory addresses; stores of 0x8000_0001_FFFF_FFFE and
0x7FFF_FFFF_8000_0080 (distinct words, every narrow sign bit exercised).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/memk_i64_1622_differential.py
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
from unicorn.arm_const import (UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R1,
                               UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4,
                               UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11,
                               UC_ARM_REG_R12, UC_ARM_REG_PC, UC_ARM_REG_SP)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
R_ARM_ABS32 = 2
R_ARM_THM_CALL = 10
BASES = {".text": 0x0010_0000, ".bss": 0x0040_0000, ".data": 0x0080_0000,
         ".synth.wasm_mem_1": 0x0100_0000}
GLOBALS_BASE = 0x0300_0000
STACK_BASE, STACK_SIZE = 0x0200_0000, 0x1_0000
GARBAGE = 0xDEADBEEF
MODES = {
    "npa": ["--native-pointer-abi"],
    "plain": ["--embedder-data-init", "--embedder-global-init"],
}
TARGETS = ["cortex-m3", "cortex-m4f", "cortex-m7"]
OFFSETS = [0, 8, 16, 24, 28, 48, 108]
NARROW_LOADS = ["8_s", "8_u", "16_s", "16_u", "32_s", "32_u"]
NARROW_STORES = [("8", 1), ("16", 2), ("32", 4)]
V1 = 0x8000_0001_FFFF_FFFE
V2 = 0x7FFF_FFFF_8000_0080
SEED_LEN = 256


def seed_bytes(salt):
    return bytes(((i * 37 + salt) & 0xFF) | (0x80 if i % 3 == 0 else 0)
                 for i in range(SEED_LEN))


def esc(b):
    return "".join(f"\\{x:02x}" for x in b)


def build_fixture(mem0_decl, mem1_decl, mem1_bytes):
    """Generate the module and its call list. Returns (wat, funcs, calls)."""
    fns, funcs, calls = [], {}, []
    for off in OFFSETS:
        for al, aname in ((2, "a4"), (3, "a8")):
            n = f"ld64_o{off}_{aname}"
            fns.append(f'(func (export "{n}") (param $p i32) (result i64) '
                       f'(i64.load $m1 offset={off} align={1 << al} (local.get $p)))')
            funcs[n] = {1}
            n2 = f"st64_o{off}_{aname}"
            fns.append(f'(func (export "{n2}") (param $p i32) (param $v i64) '
                       f'(i64.store $m1 offset={off} align={1 << al} (local.get $p) (local.get $v)))')
            funcs[n2] = {1}
        for w in NARROW_LOADS:
            n = f"ld{w.replace('_', '')}_o{off}"
            fns.append(f'(func (export "{n}") (param $p i32) (result i64) '
                       f'(i64.load{w} $m1 offset={off} (local.get $p)))')
            funcs[n] = {1}
        for w, _ in NARROW_STORES:
            n = f"st{w}_o{off}"
            fns.append(f'(func (export "{n}") (param $p i32) (param $v i64) '
                       f'(i64.store{w} $m1 offset={off} (local.get $p) (local.get $v)))')
            funcs[n] = {1}
    # Pair pressure: a memory-1 i64 load live across an i64 add and a store.
    fns.append('(func (export "rmw") (param $p i32) (param $v i64) (result i64) (local $t i64) '
               '(local.set $t (i64.load $m1 offset=8 align=4 (local.get $p))) '
               '(i64.store $m1 offset=16 (local.get $p) (i64.add (local.get $t) (local.get $v))) '
               '(i64.xor (local.get $t) (local.get $v)))')
    funcs["rmw"] = {1}
    # Cross-memory transfers: memory-0 pointer (native under npa) and memory-1 offset.
    fns.append('(func (export "x01") (param $p0 i32) (param $p1 i32) '
               '(i64.store $m1 offset=16 (local.get $p1) (i64.load $m0 offset=4 (local.get $p0))))')
    fns.append('(func (export "x10") (param $p0 i32) (param $p1 i32) '
               '(i64.store $m0 offset=8 (local.get $p0) (i64.load $m1 offset=24 align=4 (local.get $p1))))')
    funcs["x01"] = {0, 1}
    funcs["x10"] = {0, 1}
    wat = ("(module\n"
           f"  (memory $m0 {mem0_decl})\n"
           f"  (memory $m1 {mem1_decl})\n"
           f'  (data (memory $m1) (i32.const 0x0) "{esc(seed_bytes(0x81))}")\n'
           + "".join(f"  {f}\n" for f in fns) + ")")

    end = mem1_bytes
    # Loads first (read the seed), then stores, then loads again (read stores).
    def loads():
        out = []
        for off in OFFSETS:
            for aname in ("a4", "a8"):
                for p in (0, 3, 0x41, end - off - 8):
                    out.append((f"ld64_o{off}_{aname}", [("i32", p)], "i64"))
            for w in NARROW_LOADS:
                width = int(w.split("_")[0]) // 8
                for p in (0, 1, 0x43, end - off - width):
                    out.append((f"ld{w.replace('_', '')}_o{off}", [("i32", p)], "i64"))
        return out
    calls += loads()
    for off in OFFSETS:
        for aname in ("a4", "a8"):
            for p, v in ((0x20, V1), (0x31, V2), (end - off - 8, V1)):
                calls.append((f"st64_o{off}_{aname}", [("i32", p), ("i64", v)], None))
        for w, width in NARROW_STORES:
            for p, v in ((0x50, V1), (0x63, V2), (end - off - width, V2)):
                calls.append((f"st{w}_o{off}", [("i32", p), ("i64", v)], None))
    calls += [(n, a, r) for n, a, r in loads() if a[0][1] in (0, 0x41, 0x43)]
    calls += [("rmw", [("i32", 0x10), ("i64", V1)], "i64"),
              ("rmw", [("i32", 0x23), ("i64", V2)], "i64"),
              # memory 0 carries no data segment (an NPA object without a
              # memory-0 static reference refuses one), so x10 seeds it first
              ("x10", [("n0", 0x100), ("i32", 0x20)], None),
              ("x10", [("n0", 0x113), ("i32", 0x31)], None),
              ("x01", [("n0", 0x104), ("i32", 0x200)], None),
              ("x01", [("n0", 0x115), ("i32", 0x301)], None),
              ("ld64_o16_a8", [("i32", 0x200)], "i64"),
              ("ld64_o16_a8", [("i32", 0x301)], "i64")]
    return wat, funcs, calls


FIXTURES = [
    ("gale", "2080 2080 (pagesize 1)", "5376 5376 (pagesize 1)", 5376),
    ("paged", "1 1", "1 1", 65536),
]


def wat_bytes(lit):
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


def compile_obj(wat, tmp, label, mode, target):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}.{mode}.{target}.o"
    if obj.exists():
        obj.unlink()
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", target,
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
    def __init__(self, obj, mode, wat):
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
        self.mem1_size = self.abs["__synth_mem_size_1"]
        if mode == "plain" or ".bss" not in self.sizes:
            self.sizes[".bss"] = self.mem0_size
            blobs[".bss"] = b""
            self.syms["__synth_wasm_data"] = (".bss", 0, 0)
        text = bytearray(blobs[".text"])
        self.text = bytes(blobs[".text"])
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
            for off, b in segments(wat, 0):  # the harness is the embedder
                self.mu.mem_write(BASES[".bss"] + off, b)
        self.segs0 = segments(wat, 0)
        self.seg_syms = sorted(
            (int(n[len("__synth_wasm_seg_"):]), self.addr(n))
            for n in self.syms if n.startswith("__synth_wasm_seg_"))
        self.accesses = []
        self.mu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, self._hook)

    def _hook(self, uc, acc, addr, size, val, ud):
        self.accesses.append((uc.reg_read(UC_ARM_REG_PC), addr, size))

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
                return 0 if name == ".bss" else 1
        if STACK_BASE <= a < STACK_BASE + STACK_SIZE:
            return "stack"
        if GLOBALS_BASE <= a < GLOBALS_BASE + 0x1000:
            return "globals"
        return f"OUTSIDE@{a:#x}"

    def func_of(self, pc):
        for lo, hi, name in self.funcs:
            if lo <= pc < hi and not name.startswith("func_"):
                return name
        return f"pc@{pc:#x}"

    def native0(self, off):
        if self.mode != "npa":
            return off
        for k2, a in reversed(self.seg_syms):
            soff, b = self.segs0[k2]
            if soff <= off < soff + len(b):
                return a + (off - soff)
        return self.addr("__synth_wasm_data") + off

    def call(self, fn, args, ret):
        sec, val, _ = self.syms[fn]
        regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
        for i, r in enumerate(regs):
            self.mu.reg_write(r, GARBAGE ^ i)
        for i in range(5):  # r4..r8 garbage; r9..r11 are the ABI registers
            self.mu.reg_write(UC_ARM_REG_R4 + i, GARBAGE ^ (0x100 * i))
        ncrn = 0
        for ty, v in args:
            if ty == "i64":
                ncrn += ncrn & 1  # AAPCS: an i64 starts at an even register
                self.mu.reg_write(regs[ncrn], v & 0xFFFFFFFF)
                self.mu.reg_write(regs[ncrn + 1], (v >> 32) & 0xFFFFFFFF)
                ncrn += 2
            else:
                self.mu.reg_write(regs[ncrn], (self.native0(v) if ty == "n0" else v) & 0xFFFFFFFF)
                ncrn += 1
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
        lo = self.mu.reg_read(UC_ARM_REG_R0)
        if ret == "i64":
            return lo | (self.mu.reg_read(UC_ARM_REG_R1) << 32)
        return None

    def mem_image(self, k, n):
        if k > 0:
            return bytes(self.mu.mem_read(BASES[".synth.wasm_mem_1"], n))
        img = bytearray(self.mu.mem_read(BASES[".bss"], min(n, self.sizes[".bss"])))
        img += bytes(n - len(img))
        if self.mode == "npa":
            for k2, a in self.seg_syms:
                off, b = self.segs0[k2]
                img[off:off + len(b)] = self.mu.mem_read(a, len(b))
        return bytes(img)


def wasmtime_instance(wat):
    wat_x = wat
    for k in range(2):
        wat_x = wat_x.replace(f"(memory $m{k} ", f"(memory $m{k} (export \"m{k}\") ", 1)
    cfg = wasmtime.Config()
    cfg.wasm_multi_memory = True
    cfg.wasm_custom_page_sizes = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    ex = wasmtime.Instance(st, wasmtime.Module(eng, wat_x), []).exports(st)
    return st, ex, [ex["m0"], ex["m1"]]


def run(label, wat, funcs, calls, extent1, mode, target, tmp):
    rc, log, obj = compile_obj(wat, tmp, label, mode, target)
    if rc != 0:
        tail = [ln for ln in log.splitlines() if "rror" in ln or "skipping" in ln]
        print(f"[RED] {label}/{mode}/{target}: compile rc={rc}: "
              f"{len(tail)} error/skip line(s); first: {tail[0][:300] if tail else '-'}")
        return 0, 1, None
    ln = Linked(obj, mode, wat)
    fails = 0
    if ln.mem1_size != extent1:
        print(f"  [BUG] {label}/{mode}/{target}: __synth_mem_size_1 = {ln.mem1_size} "
              f"!= declared extent {extent1}")
        fails += 1
    st, ex, wm = wasmtime_instance(wat)
    compared = 0
    for fn, args, ret in calls:
        try:
            res = ex[fn](st, *[v for _, v in args])
            exp = None if res is None else res & 0xFFFF_FFFF_FFFF_FFFF
        except wasmtime.Trap:
            exp = "trap"
        got = ln.call(fn, args, ret)
        ok = (exp == "trap" and isinstance(got, str)) or (
            not isinstance(got, str) and got == exp)
        breach = []
        for pc, a, size in ln.accesses:
            m = ln.mem_of(a)
            f = ln.func_of(pc)
            if isinstance(m, str) and m.startswith("OUTSIDE"):
                breach.append(f"{f}:{m}")
            elif isinstance(m, int) and m not in funcs.get(f, set()):
                breach.append(f"{f}:m{m}")
            elif m == 1 and not (BASES[".synth.wasm_mem_1"] <= a
                                 and a + size <= BASES[".synth.wasm_mem_1"] + ln.mem1_size):
                breach.append(f"{f}:m1-straddle@{a:#x}")
        sizes = [w.data_len(st) for w in wm]
        same = [ln.mem_image(k, sizes[k]) == bytes(wm[k].read(st, 0, sizes[k]))
                for k in range(2)]
        good = ok and not breach and all(same)
        compared += 1
        fails += not good
        if not good:
            shown = got if isinstance(got, str) else (None if got is None else hex(got))
            print(f"  [BUG] {label}/{mode}/{target}.{fn}{tuple(v for _, v in args)} -> {shown} "
                  f"(wasmtime {exp if exp in (None, 'trap') else hex(exp)})"
                  f"{'  RESULT' if not ok else ''}"
                  f"{'  ISOLATION ' + ','.join(sorted(set(breach))[:4]) if breach else ''}"
                  + "".join(f"  MEM{k}" for k in range(2) if not same[k]))
    print(f"  {label}/{mode}/{target}: {compared} calls, {fails} mismatch(es)")
    return compared, fails, ln.text


def main():
    tmp = Path(tempfile.mkdtemp(prefix="memk_i64_1622_"))
    total = fails = 0
    for label, d0, d1, extent1 in FIXTURES:
        wat, funcs, calls = build_fixture(d0, d1, extent1)
        for mode in MODES:
            texts = {}
            for target in TARGETS:
                c, f, text = run(label, wat, funcs, calls, extent1, mode, target, tmp)
                total += c
                fails += f
                if text is not None:
                    texts[target] = text
            if len(texts) == len(TARGETS):
                same = len(set(texts.values())) == 1
                print(f"  {label}/{mode}: .text byte-identical across "
                      f"{'/'.join(TARGETS)}: {'yes' if same else 'no'}")
    if total < 5388:
        print(f"VACUOUS: compared {total} calls")
        return 1
    print(f"\ncompared: {total}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
