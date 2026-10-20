#!/usr/bin/env python3
# ci-status: manual (external-input) — needs the reporter's c.loom.wasm (pulseengine/jess repro/synth-1436/, sha256 791ab6b5c8f661e562058ab99fc9a47fc172483f8aacb67758bb660777ece368), which is not vendored in this tree; the defect it localised is gated in CI by vfp_home_alias_1436_differential.py (wired).
"""RQ-88-JESSDIVERGE10 (#1436) — localise the reporter's divergence by EXECUTION.

Three phases over the reporter's own module, compiled with the README's command
(`-t cortex-m7dp --cortex-m --relocatable --all-exports --embedder-data-init
--embedder-global-init`) and run under unicorn as the embedder: R11 = linear
memory with the active data segments applied, R9 = the dense globals table with
their init values, R10 = 64 KiB. IMU = (0, 0, -9.81, 0.30, -0.15, 0.07), the
reporter's vector.

  1. POSITIVE CONTROL against the reporter's QEMU trace. The three gravity
     blocks are located by SHAPE (`vldr s8,[sp,#A]; vldr s9,[sp,#M]`), each
     word is sampled at its own load pc, and ticks 1/2/8/16 are compared with
     the 36 words of their table (gravity-blocks-16ticks.md). The reads of the
     three result slots are counted per pc (they report 240 each, from one
     consumer, ELF pc 0x33c0 = object 0x30dc). With --veld-file, every vel-d
     word (return area +36) is compared with their 1024-tick trace.
  2. FIRST DIVERGENT STORE. Every wasm store and bulk op is rewritten to call a
     logging helper (wasmtime side; appended functions, so no existing index
     moves), every linear-memory write is hooked on the ARM side, and the k-th
     write of each byte is compared. The earliest wasm event that disagrees is
     printed with its site and the ARM pc that wrote the other value.
  3. FULL STATE. All 14 return words every tick and all 16384 linear-memory
     words at the end, against wasmtime.

MEASURED at 0.87.0 (unfixed): phase 1 matches all 36 table words and all 1024
vel-d words bit-exact (final 0x41221afe); phase 2 names wasm func 2's
`f32.store offset=1448` (frame 0xfb0 + 1448 = 0x1558): wasm 0x00000000, ARM
0x411cf5c3 written at object pc 0x748 — the stale `local.tee 18` read; phase 3
differs on every tick. With the #1436 float-home detach: phases 2 and 3 find
ZERO differences at 16 and 1024 ticks, and phase 1's gravity words are
unchanged (those blocks were never wrong).

Run:  python3 -I scripts/repro/jessdiverge10_localise_1436.py \\
        --wasm <dir>/c.loom.wasm --synth ./target/release/synth [--ticks 16] \\
        [--veld-file <dir>/veld-arm-1024ticks.txt]
Needs wasmtime, unicorn, pyelftools, wasm-tools and arm-none-eabi-objdump.
"""
import argparse
import hashlib
import json
import re
import struct
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC, UC_ARM_REG_IP, UC_ARM_REG_LR, UC_ARM_REG_PC,
    UC_ARM_REG_R0, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11, UC_ARM_REG_S0, UC_ARM_REG_SP,
)

SHA = "791ab6b5c8f661e562058ab99fc9a47fc172483f8aacb67758bb660777ece368"
EST = "pulseengine:falcon-cascade/ekf@0.10.0#estimate"
IMU = [0.0, 0.0, -9.81, 0.30, -0.15, 0.07]
CODE, LIN, GLOB, STACK, SSZ, RET = 0x100000, 0x20000000, 0x30000000, 0x40000000, 0x100000, 0x80000
# The reporter's table, (tick, block) -> (addend, multiplicand, stored result).
TABLE = {
    (1, 0): (0x00000000, 0x399d489e, 0x3b40de7d), (1, 1): (0x00000000, 0x391d4c24, 0x3ac0e2cf),
    (1, 2): (0xc11cf5c3, 0x3f7fffff, 0xb5800000), (2, 0): (0x00000000, 0x39d30f06, 0x3b8167c6),
    (2, 1): (0x00000000, 0x39531629, 0x3b016c26), (2, 2): (0xc11cf5c3, 0x3f7ffffe, 0xb5800000),
    (8, 0): (0x00000000, 0x3aa81fb4, 0x3c4e2970), (8, 1): (0x00000000, 0x3a2833fe, 0x3bce4251),
    (8, 2): (0xc11cf5c3, 0x3f7fffef, 0xb7200000), (16, 0): (0x00000000, 0x3b22754a, 0x3cc736de),
    (16, 1): (0x00000000, 0x3aa29c3b, 0x3c47669f), (16, 2): (0xc11cf5c3, 0x3f7fffc0, 0xb81c0000),
}
BLOCK_OFFSETS = ((200, 152), (216, 232), (192, 208))


# ---- wasm module facts (globals, active data) -------------------------------
def _uleb(b, p):
    r = s = 0
    while True:
        x = b[p]; p += 1; r |= (x & 0x7F) << s; s += 7
        if not x & 0x80:
            return r, p


def _sleb(b, p):
    r = s = 0
    while True:
        x = b[p]; p += 1; r |= (x & 0x7F) << s; s += 7
        if not x & 0x80:
            return (r - (1 << s) if x & 0x40 else r), p


def _i32_const(b, p):
    assert b[p] == 0x41, "only i32.const initialisers are modelled"
    v, p = _sleb(b, p + 1)
    assert b[p] == 0x0B
    return v & 0xFFFFFFFF, p + 1


def module_facts(wasm):
    b = Path(wasm).read_bytes(); p = 8; glob, data = [], []
    while p < len(b):
        sid = b[p]; ln, p = _uleb(b, p + 1); end = p + ln
        if sid == 6:
            n, q = _uleb(b, p)
            for _ in range(n):
                v, q = _i32_const(b, q + 2); glob.append(v)
        elif sid == 11:
            n, q = _uleb(b, p)
            for _ in range(n):
                flag, q = _uleb(b, q); assert flag == 0
                off, q = _i32_const(b, q); ln2, q = _uleb(b, q)
                data.append((off, b[q:q + ln2])); q += ln2
        p = end
    return glob, data


# ---- the ARM side -------------------------------------------------------------
def _thm_bl(pc, target):
    off = (target - (pc + 4)) & 0x01FFFFFF
    s, i1, i2 = (off >> 24) & 1, (off >> 23) & 1, (off >> 22) & 1
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return 0xF000 | (s << 10) | ((off >> 12) & 0x3FF), 0xD000 | (j1 << 13) | (j2 << 11) | ((off >> 1) & 0x7FF)


class Emu:
    def __init__(self, obj, wasm):
        e = ELFFile(open(obj, "rb"))
        symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        self.syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
        text = bytearray(e.get_section_by_name(".text").data())
        for rel in e.iter_sections():
            if rel["sh_type"] not in ("SHT_REL", "SHT_RELA"):
                continue
            for r in rel.iter_relocations():
                assert r["r_info_type"] == 10, f"unmodelled reloc {r['r_info_type']}"
                tgt = self.syms[symtab.get_symbol(r["r_info_sym"]).name] & ~1
                struct.pack_into("<HH", text, r["r_offset"], *_thm_bl(CODE + r["r_offset"], CODE + tgt))
        glob, data = module_facts(wasm)
        mu = self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, (len(text) + 0xFFF) & ~0xFFF); mu.mem_write(CODE, bytes(text))
        mu.mem_map(RET, 0x1000); mu.mem_map(LIN, 0x10000); mu.mem_map(GLOB, 0x1000); mu.mem_map(STACK, SSZ)
        for off, blob in data:
            mu.mem_write(LIN + off, bytes(blob))
        for i, v in enumerate(glob):
            mu.mem_write(GLOB + 4 * i, struct.pack("<I", v))
        mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000); mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)

    def estimate(self):
        mu = self.mu
        mu.reg_write(UC_ARM_REG_SP, STACK + SSZ - 0x100)
        mu.reg_write(UC_ARM_REG_R9, GLOB); mu.reg_write(UC_ARM_REG_R10, 0x10000); mu.reg_write(UC_ARM_REG_R11, LIN)
        for i, v in enumerate(IMU):
            mu.reg_write(UC_ARM_REG_S0 + i, struct.unpack("<I", struct.pack("<f", v))[0])
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        mu.emu_start((CODE + (self.syms[EST] & ~1)) | 1, RET, count=50_000_000)
        assert mu.reg_read(UC_ARM_REG_PC) & ~1 == RET, "did not return"
        return mu.reg_read(UC_ARM_REG_R0)

    def rd(self, a, n):
        return bytes(self.mu.mem_read(LIN + a, n))


def wasm_instance(wasm_bytes):
    e = wasmtime.Engine(); st = wasmtime.Store(e)
    inst = wasmtime.Instance(st, wasmtime.Module(e, wasm_bytes), [])
    return st, inst.exports(st)[EST], inst.exports(st)["memory"]


# ---- phase 1 ------------------------------------------------------------------
def phase1(obj, wasm, ticks, veld_file):
    dis = subprocess.run(["arm-none-eabi-objdump", "-d", obj], capture_output=True, text=True, check=True).stdout

    def pcs(pat):
        return [int(m.group(1), 16) for m in re.finditer(r"^\s*([0-9a-f]+):\s+[0-9a-f ]+\s+" + pat, dis, re.M)]
    cands = []
    for a, m in BLOCK_OFFSETS:
        loads9 = set(pcs(r"vldr\s+s9, \[sp, #%d\]" % m))
        cands.append([p for p in pcs(r"vldr\s+s8, \[sp, #%d\]" % a) if p + 4 in loads9])
    stores = pcs(r"str\.w\s+r\d, \[fp, ip\]")
    blocks = []
    for (a, m), c in zip(BLOCK_OFFSETS, cands):
        p = [p for p in c if any(0 <= p - f < 0x60 for f in cands[0])][0]
        blocks.append((p, a, m, [q for q in stores if p < q < p + 0x30][0]))
    print("phase 1: gravity blocks (vldr pc, addend, multiplicand, store pc):",
          [(hex(p), a, m, hex(s)) for p, a, m, s in blocks])
    em = Emu(obj, wasm); mu = em.mu; rec = {}; tick = [0]; reads = defaultdict(int); slots = set()

    def code(uc, addr, size, _):
        pc, sp = addr - CODE, uc.reg_read(UC_ARM_REG_SP)
        for k, (p, a, m, st) in enumerate(blocks):
            if pc == p:
                rec[(tick[0], k)] = [struct.unpack("<I", uc.mem_read(sp + o, 4))[0] for o in (a, m)]
            if pc == st:
                rt = (struct.unpack("<I", uc.mem_read(addr, 4))[0] >> 28) & 0xF
                rec[(tick[0], k)] += [uc.reg_read(UC_ARM_REG_R0 + rt), uc.reg_read(UC_ARM_REG_IP)]
                slots.add(uc.reg_read(UC_ARM_REG_IP))
    mu.hook_add(UC_HOOK_CODE, code, begin=CODE + blocks[0][0], end=CODE + blocks[-1][3] + 4)

    def rhook(uc, acc, addr, size, val, _):
        if addr - LIN in slots:
            reads[(addr - LIN, uc.reg_read(UC_ARM_REG_PC) - CODE)] += 1
    mu.hook_add(UC_HOOK_MEM_READ, rhook, begin=LIN, end=LIN + 0x10000)
    veld = []; mismatches = 0
    for t in range(1, ticks + 1):
        tick[0] = t; r = em.estimate()
        veld.append(struct.unpack("<I", em.rd(r + 36, 4))[0])
    for (t, k), want in sorted(TABLE.items()):
        if t > ticks:
            continue
        a, m, res, addr = rec[(t, k)]
        ok = (a, m, res) == want; mismatches += not ok
        print(f"  {'ok  ' if ok else 'DIFF'} tick {t:2d} blk{k + 1} addend {a:08x} mult {m:08x} "
              f"result {res:08x} -> lin {addr:#x}  (reporter {want[0]:08x} {want[1]:08x} {want[2]:08x})")
    print("  result-slot reads by (slot, object pc):", {(hex(a), hex(p)): n for (a, p), n in sorted(reads.items())})
    if veld_file:
        # Data lines only: the file's '#' header itself quotes a word (the
        # final value), which a token scan would count as tick 1.
        theirs = [int(ln, 16) for ln in Path(veld_file).read_text().splitlines()
                  if re.fullmatch(r"[0-9a-f]{8}", ln.strip())]
        n = min(len(theirs), len(veld))
        same = sum(1 for i in range(n) if theirs[i] == veld[i])
        print(f"  vel-d vs reporter trace: {same}/{n} words identical; last ours {veld[n - 1]:08x} theirs {theirs[n - 1]:08x}")
    return mismatches


# ---- phase 2 ------------------------------------------------------------------
STORE_RE = re.compile(r"^(\s+)(i32|i64|f32|f64)\.(store(8|16|32)?)((?: offset=\d+)?)((?: align=\d+)?)\s*$")
WIDTH = {"store": None, "store8": 1, "store16": 2, "store32": 4}
NATURAL = {"i32": 4, "f32": 4, "i64": 8, "f64": 8}


def instrument(wat):
    out, sites, need, func = [], [], set(), -1
    for ln in wat.split("\n"):
        if ln.startswith("  (func "):
            func += 1
        m = STORE_RE.match(ln)
        if m:
            ind, ty, op, _, off, _ = m.groups()
            o = int(off.split("=")[1]) if off else 0
            need.add(f"{ty}_{op}"); sites.append((func, ln.strip()))
            out += [f"{ind}i32.const {o}", f"{ind}i32.const {len(sites) - 1}", f"{ind}call $log_{ty}_{op}"]
            continue
        s = ln.strip()
        if s in ("memory.copy", "memory.fill"):
            ind = ln[: len(ln) - len(ln.lstrip())]
            sites.append((func, s))
            out += [f"{ind}i32.const {len(sites) - 1}", f"{ind}call $log_{s.replace('.', '_')}"]
            continue
        out.append(ln.replace("(memory (;0;) 1)", "(memory (;0;) 64)"))
    helpers = ["  (global $logp (mut i32) i32.const 65536)"]
    for key in sorted(need):
        ty, op = key.split("_"); n = WIDTH[op] or NATURAL[ty]
        helpers.append(f"""  (func $log_{key} (param $a i32) (param $v {ty}) (param $o i32) (param $s i32) (local $ea i32)
    local.get $a local.get $o i32.add local.set $ea
    local.get $ea local.get $v {ty}.{op}
    global.get $logp local.get $s i32.store
    global.get $logp local.get $ea i32.store offset=4
    global.get $logp i32.const {n} i32.store offset=8
    global.get $logp i32.const 12 i32.add local.get $ea i32.const {n} memory.copy
    global.get $logp i32.const {12 + ((n + 3) // 4) * 4} i32.add global.set $logp)""")
    for k, op in (("memory_copy", "copy"), ("memory_fill", "fill")):
        helpers.append(f"""  (func $log_{k} (param $d i32) (param $x i32) (param $n i32) (param $s i32)
    local.get $d local.get $x local.get $n memory.{op}
    global.get $logp local.get $s i32.store
    global.get $logp local.get $d i32.store offset=4
    global.get $logp local.get $n i32.store offset=8
    global.get $logp i32.const 12 i32.add local.get $d local.get $n memory.copy
    global.get $logp i32.const 12 i32.add local.get $n i32.const 3 i32.add i32.const -4 i32.and i32.add global.set $logp)""")
    i = [j for j, l in enumerate(out) if l.startswith("  (data ")][0]
    return "\n".join(out[:i] + helpers + out[i:]), sites


def phase2(obj, wasm, ticks):
    wat = subprocess.run(["wasm-tools", "print", wasm], capture_output=True, text=True, check=True).stdout
    iwat, sites = instrument(wat)
    st, f, mem = wasm_instance(wasmtime.wat2wasm(iwat))
    for _ in range(ticks):
        f(st, *IMU)
    raw = bytes(mem.read(st, 0x10000, 64 * 0x10000)); wev, p = [], 0
    while True:
        s, a, n = struct.unpack_from("<iII", raw, p)
        if (s, a, n) == (0, 0, 0):
            break
        wev.append((s, a, raw[p + 12:p + 12 + n])); p += 12 + ((n + 3) // 4) * 4
    em = Emu(obj, wasm); aev = []

    def hk(uc, acc, addr, size, val, _):
        if LIN <= addr < LIN + 0x10000:
            aev.append((uc.reg_read(UC_ARM_REG_PC) - CODE, addr - LIN, (val & ((1 << (8 * size)) - 1)).to_bytes(size, "little")))
    em.mu.hook_add(UC_HOOK_MEM_WRITE, hk)
    for _ in range(ticks):
        em.estimate()

    def expand(ev):
        cnt, res = defaultdict(int), {}
        for i, (tag, a, b) in enumerate(ev):
            for j, x in enumerate(b):
                k = cnt[a + j]; cnt[a + j] += 1; res[(a + j, k)] = (i, x, tag)
        return res, cnt
    W, wc = expand(wev); A, ac = expand(aev)
    first = None
    for key, (i, x, tag) in W.items():
        y = A.get(key)
        if (y is None or y[1] != x) and (first is None or i < first[0]):
            first = (i, key, x, y, tag)
    count_diff = sum(1 for k in set(wc) | set(ac) if wc[k] != ac[k])
    print(f"phase 2: {len(wev)} wasm store events, {len(aev)} ARM writes over {ticks} tick(s); "
          f"bytes with differing write counts: {count_diff}")
    if first is None:
        print("  NO divergent store")
        return 0
    i, (addr, k), x, y, tag = first
    func, site = sites[tag]
    print(f"  FIRST divergent store: wasm event #{i}, func {func} `{site}`, lin {addr:#x} (write #{k}): "
          f"wasm byte {x:02x}, ARM " + (f"{y[1]:02x} written at object pc {aev[y[0]][0]:#x}" if y else "never wrote it"))
    s0, a0, b0 = wev[i]
    print(f"  that store's full value: wasm {b0[::-1].hex()} at lin {a0:#x}")
    return 1


# ---- phase 3 ------------------------------------------------------------------
def phase3(obj, wasm, ticks):
    st, f, mem = wasm_instance(Path(wasm).read_bytes()); em = Emu(obj, wasm); bad, first = 0, None
    for t in range(1, ticks + 1):
        rw, ra = f(st, *IMU), em.estimate()
        if rw != ra or bytes(mem.read(st, rw, rw + 56)) != em.rd(ra, 56):
            bad += 1; first = first or t
        if t in (1, ticks):
            print(f"  tick {t}: vel-d wasm {bytes(mem.read(st, rw + 36, rw + 40))[::-1].hex()} "
                  f"ARM {em.rd(ra + 36, 4)[::-1].hex()}")
    A, B = bytes(mem.read(st, 0, 0x10000)), em.rd(0, 0x10000)
    nd = sum(1 for i in range(0, 0x10000, 4) if A[i:i + 4] != B[i:i + 4])
    print(f"phase 3: {ticks} ticks — return areas differing on {bad} tick(s) (first {first}); "
          f"linear-memory words differing at the end: {nd} of 16384")
    return bad + nd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wasm", required=True); ap.add_argument("--synth", required=True)
    ap.add_argument("--ticks", type=int, default=16); ap.add_argument("--veld-file")
    a = ap.parse_args()
    got = hashlib.sha256(Path(a.wasm).read_bytes()).hexdigest()
    if got != SHA:
        sys.exit(f"REFUSE: {a.wasm} sha256 {got} is not the reporter's module {SHA}")
    with tempfile.TemporaryDirectory() as td:
        obj = str(Path(td) / "cascade.o")
        r = subprocess.run([a.synth, "compile", a.wasm, "-t", "cortex-m7dp", "--cortex-m", "--relocatable",
                            "--all-exports", "--embedder-data-init", "--embedder-global-init", "-o", obj],
                           capture_output=True, text=True)
        print(f"compile rc={r.returncode}")
        if r.returncode:
            print(r.stdout + r.stderr); return 1
        p1 = phase1(obj, a.wasm, max(a.ticks, 16) if not a.veld_file else 1024, a.veld_file)
        p2 = phase2(obj, a.wasm, 1)
        p3 = phase3(obj, a.wasm, a.ticks)
        print(json.dumps({"positive_control_mismatches": p1, "divergent_store_found": bool(p2),
                          "phase3_differences": p3}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
