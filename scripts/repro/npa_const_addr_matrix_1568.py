#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 99
"""The #1568 constant-address matrix under --native-pointer-abi, executed
against wasmtime — the generator behind the v0.88 "81 wrong of 162" figures.

PROVENANCE. The v0.88 NPACONST lane (PR #1569, squash 85914929) measured its
before/after figures with two scratch scripts that were never committed
(`probe_matrix.py` wrote the modules, `exec_matrix.py` executed them; #1574,
v0.88 cold review R1-1 / R2-3). Both were recovered verbatim from that lane's
session record and are merged here in their FINAL state. Kept as they were,
because changing them would change the figures:
  - the WAT template (memory 2; four data segments at 0x100, 0x1000, 0x2800
    and 0x10000 in EVERY module; an `anchor` export that loads 0x100, or
    0x2800 in the spsliver kind);
  - the target: cortex-m7dp for the f32/f64 families, cortex-m3 otherwise;
  - the verdict: the function result (r0/r1, or the S0/D0 bit pattern for
    f32/f64), then every byte of every data segment, compared after one call
    of `f`. Synth's copy of linear address `a` is read through the later-wins
    `__synth_wasm_seg_K` symbol that holds it, else `__synth_wasm_data + a`;
  - the harness: the hand linker of `npa_const_addr_differential.py`
    (.text/.data/.bss at separate bases, R11 = 0, one fresh instance per cell).
dropped: the objdump `[fp, ...]` probe, which was diagnostic only and never fed
a count.

THE AXES, and which are partial. "19 families x 4 shapes x 3 kinds" (CHANGELOG
[0.88.0], 85914929) is 228, not 162; the real product is below.
  families (19): i32.load, i32.load8_u, i32.load16_s, i32.store, i32.store8,
      i32.store16, i64.load, i64.load8_u, i64.load32_s, i64.store, i64.store16,
      i64.store32, f32.load, f32.store, f64.load, f64.store, memory.fill,
      memory.copy_dst, memory.copy_src
  shapes (FIVE, not four): le_fff  `i32.const 0x100`
                           gt_fff  `i32.const 0x1004`
                           gt_ffff `i32.const 0x10004`
                           off_gt_fff `i32.const 0 ... offset=0x1004`
                           sliver  `i32.const 0x1800 ... offset=0x1000`
  kinds (3): nosp     no stack-pointer global      shapes le_fff..off_gt_fff
             sp       SP global at 0x80            shapes le_fff..off_gt_fff
             spsliver SP global at 0x2000          shape  sliver only
  PARTIAL AXIS 1: the three memory.* families have no memarg, so every shape
      that carries an `offset=` is skipped for them (off_gt_fff, sliver).
  PARTIAL AXIS 2: the shape set depends on the kind (sliver only in spsliver).
  So: nosp 16x4 + 3x3 = 73, sp 73, spsliver 16x1 = 16; total 162.

VERDICTS per cell: ok, WRONG (compiled clean, result or a segment byte differs
from wasmtime, or the emulator faulted), REFUSED (non-zero exit; sub-reason
`npa-guard` when the log carries the npa_const_addr_guard needle, else
`other`), HARNESS (the object could not be linked by this harness — never
counted as a synth verdict, always fatal).

Modes:
  SYNTH=bin python3 npa_const_addr_matrix_1568.py [--expect ok=N,refused=N,guard=N]
      run the matrix; exit 1 on any WRONG, any HARNESS, a population other
      than 162, or a count differing from --expect (exact, both directions;
      `guard` = refusals carrying the npa_const_addr_guard needle).

MEASURED (v0.89, #1574), all three binaries built from their commits:
  pre-fix  f982481f: ok 75, WRONG 81, REFUSED 6 (all GI-FPU-002 declines)
  post-fix 85914929: ok 99, WRONG 0,  REFUSED 63 (npa-guard 59, other 4)
      transitions: ok->ok 75, WRONG->ok 24, WRONG->REFUSED 57 (all 57 by the
      npa guard), REFUSED->REFUSED 6 (2 now by the npa guard, 4 still
      GI-FPU-002); nothing that was ok changed.
  main     9f123a65: identical to 85914929, cell for cell.
  WRONG at the pre-fix binary by kind: nosp 65, spsliver 16, sp 0.
CI runs it with --expect ok=99,refused=63,guard=59,wrong=0; a reach change
that moves a cell moves the pin in the same PR.
  python3 npa_const_addr_matrix_1568.py --before BIN_A --after BIN_B
      run both and print the per-cell transition table (the 24/57/0 figures).
  --json OUT  write the per-cell verdicts.
Needs wasmtime + unicorn + pyelftools.
"""

import argparse
import json
import os
import struct
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_C1_C0_2,
    UC_ARM_REG_D0,
    UC_ARM_REG_FPEXC,
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
    UC_CPU_ARM_MAX,
)

R_ARM_ABS32 = 2
R_ARM_THM_CALL = 10
BASES = {".text": 0x10000, ".data": 0x60000, ".bss": 0x80000}
MAPSZ = 0x20000
POPULATION = 162
NEEDLE = "which this lowering would emit as a raw linear-memory offset off R11"

# (signature, body template, kind) — kind "f" selects the VFP target.
FAMILIES = {
    "i32.load": ("(result i32)", "{a} i32.load{o}", "i32"),
    "i32.load8_u": ("(result i32)", "{a} i32.load8_u{o}", "i32"),
    "i32.load16_s": ("(result i32)", "{a} i32.load16_s{o}", "i32"),
    "i32.store": ("", "{a} i32.const 7 i32.store{o}", "i32"),
    "i32.store8": ("", "{a} i32.const 7 i32.store8{o}", "i32"),
    "i32.store16": ("", "{a} i32.const 7 i32.store16{o}", "i32"),
    "i64.load": ("(result i64)", "{a} i64.load{o}", "i32"),
    "i64.load8_u": ("(result i64)", "{a} i64.load8_u{o}", "i32"),
    "i64.load32_s": ("(result i64)", "{a} i64.load32_s{o}", "i32"),
    "i64.store": ("", "{a} i64.const 7 i64.store{o}", "i32"),
    "i64.store16": ("", "{a} i64.const 7 i64.store16{o}", "i32"),
    "i64.store32": ("", "{a} i64.const 7 i64.store32{o}", "i32"),
    "f32.load": ("(result f32)", "{a} f32.load{o}", "f"),
    "f32.store": ("", "{a} f32.const 1 f32.store{o}", "f"),
    "f64.load": ("(result f64)", "{a} f64.load{o}", "f"),
    "f64.store": ("", "{a} f64.const 1 f64.store{o}", "f"),
    "memory.fill": ("", "{a} i32.const 9 i32.const 4 memory.fill", "i32"),
    "memory.copy_dst": ("", "{a} i32.const 0x104 i32.const 4 memory.copy", "i32"),
    "memory.copy_src": ("", "i32.const 0x104 {a} i32.const 4 memory.copy", "i32"),
}
SHAPES = {
    "le_fff": ("i32.const 0x100", ""),
    "gt_fff": ("i32.const 0x1004", ""),
    "gt_ffff": ("i32.const 0x10004", ""),
    "off_gt_fff": ("i32.const 0", " offset=0x1004"),
}
SLIVER = {"sliver": ("i32.const 0x1800", " offset=0x1000")}
ANCHOR = '(func (export "anchor") (result i32) (i32.load (i32.const 0x100)))'
KINDS = {
    "nosp": ANCHOR,
    "sp": "(global $sp (mut i32) (i32.const 0x80)) " + ANCHOR,
    "spsliver": "(global $sp (mut i32) (i32.const 0x2000)) "
    '(func (export "anchor") (result i32) (i32.load (i32.const 0x2800)))',
}
DATA = (
    r' (data (i32.const 0x100) "\01\02\03\04\05\06\07\08\09\0a\0b\0c\0d\0e\0f\10")'
    "\n"
    r' (data (i32.const 0x1000) "\11\12\13\14\15\16\17\18\19\1a\1b\1c\1d\1e\1f\20")'
    "\n"
    r' (data (i32.const 0x2800) "\31\32\33\34\35\36\37\38\39\3a\3b\3c\3d\3e\3f\40")'
    "\n"
    r' (data (i32.const 0x10000) "\21\22\23\24\25\26\27\28\29\2a\2b\2c\2d\2e\2f\30")'
)
# The same segments as (offset, bytes), in declaration order (later wins).
SEGS = [
    (0x100, bytes(range(0x01, 0x11))),
    (0x1000, bytes(range(0x11, 0x21))),
    (0x2800, bytes(range(0x31, 0x41))),
    (0x10000, bytes(range(0x21, 0x31))),
]


def cells():
    """Every (tag, wat, target) of the matrix, in a fixed order."""
    out = []
    for kind, extra in KINDS.items():
        for fam, (sig, body, k) in FAMILIES.items():
            for shape, (a, o) in (SLIVER if kind == "spsliver" else SHAPES).items():
                if fam.startswith("memory") and o:
                    continue  # partial axis 1: no memarg on memory.*
                wat = (f'(module (memory (export "mem") 2) {extra}\n{DATA}\n'
                       f' (func (export "f") {sig} {body.format(a=a, o=o)}))')
                tgt = "cortex-m7dp" if k == "f" else "cortex-m3"
                out.append((f"{kind}__{fam}__{shape}", wat, tgt))
    return out


class HarnessError(Exception):
    pass


def thm_bl(src, dst):
    """Encode a Thumb-2 BL from `src` (the instruction address) to `dst`."""
    off = dst - (src + 4)
    if not -(1 << 24) <= off < (1 << 24):
        raise HarnessError(f"BL out of range: {off:#x}")
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
    """Hand-link one relocatable object and map it in unicorn (R11 = 0)."""

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
                raise HarnessError(f"{name} is {size} B — larger than the map")
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
                raise HarnessError(f"unresolvable reloc target {sym.name!r}")
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
                raise HarnessError(f"unhandled reloc type {r['r_info_type']}")
        if self.abs32 == 0:
            raise HarnessError("no R_ARM_ABS32 static-data relocation (anchor)")
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.ctl_set_cpu_model(UC_CPU_ARM_MAX)
        self.mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)  # CPACR: CP10/CP11
        self.mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)  # FPEXC.EN
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
        return self.mu.reg_read(UC_ARM_REG_R0), self.mu.reg_read(UC_ARM_REG_R1)

    def image_addr(self, a):
        """Where synth keeps linear address `a`: the LAST-declared segment
        holding it, through its own symbol, else `__synth_wasm_data + a`."""
        for k in range(len(SEGS) - 1, -1, -1):
            off, b = SEGS[k]
            if off <= a < off + len(b) and f"__synth_wasm_seg_{k}" in self.syms:
                base, val = self.syms[f"__synth_wasm_seg_{k}"]
                return base + val + (a - off)
        if "__synth_wasm_data" not in self.syms:
            raise HarnessError("no __synth_wasm_data symbol")
        base, val = self.syms["__synth_wasm_data"]
        return base + val + a


def run_cell(synth, tmp, tag, wat, tgt):
    src = tmp / f"{tag}.wat"
    src.write_text(wat)
    obj = tmp / f"{tag}.o"
    if obj.exists():
        obj.unlink()
    r = subprocess.run(
        [synth, "compile", str(src), "-o", str(obj), "--target", tgt,
         "--all-exports", "--relocatable", "--native-pointer-abi"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    log = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0:
        why = "npa-guard" if NEEDLE in log else "other"
        err = [ln for ln in log.splitlines() if ln.startswith("Error")]
        return "REFUSED", why, (err[0] if err else log.strip()[-140:])[:140]
    try:
        lk = Linked(obj)
    except HarnessError as ex:
        return "HARNESS", "", str(ex)
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, wat), [])
    fn = inst.exports(st)["f"]
    res = fn(st)
    got = lk.call("f")
    if isinstance(got, str):
        return "WRONG", "", got
    nt = fn.type(st).results
    if nt:
        t = str(nt[0])
        if t == "i64":
            ok = (got[0] | (got[1] << 32)) == res & 0xFFFFFFFFFFFFFFFF
        elif t == "f32":
            v = lk.mu.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
            ok = v == struct.unpack("<I", struct.pack("<f", res))[0]
        elif t == "f64":
            v = lk.mu.reg_read(UC_ARM_REG_D0) & 0xFFFFFFFFFFFFFFFF
            ok = v == struct.unpack("<Q", struct.pack("<d", res))[0]
        else:
            ok = got[0] == res & 0xFFFFFFFF
        if not ok:
            return "WRONG", "", f"result {got} vs {res}"
    mem = inst.exports(st)["mem"]
    for off, b in SEGS:
        for i in range(len(b)):
            a = off + i
            w = mem.read(st, a, a + 1)[0]
            try:
                s = lk.mu.mem_read(lk.image_addr(a), 1)[0]
            except HarnessError as ex:
                return "HARNESS", "", str(ex)
            except UcError:
                return "WRONG", "", f"unmapped image byte {a:#x}"
            if s != w:
                return "WRONG", "", f"linmem {a:#x}: synth {s:#x} vs wasmtime {w:#x}"
    return "ok", "", ""


def run_matrix(synth):
    tmp = Path(tempfile.mkdtemp(prefix="npa_matrix_1568_"))
    return {tag: run_cell(synth, tmp, tag, wat, tgt) for tag, wat, tgt in cells()}


def summary(res):
    c = Counter(v[0] for v in res.values())
    why = Counter(v[1] for v in res.values() if v[0] == "REFUSED")
    by_kind = Counter(t.split("__")[0] for t in res)
    return c, why, by_kind


def show(label, res):
    c, why, by_kind = summary(res)
    print(f"=== {label} ===")
    print(f"population: {len(res)}  (" + ", ".join(
        f"{k} {n}" for k, n in by_kind.items()) + ")")
    print(f"ok: {c['ok']}  WRONG: {c['WRONG']}  REFUSED: {c['REFUSED']} "
          f"(npa-guard {why['npa-guard']}, other {why['other']})  "
          f"HARNESS: {c['HARNESS']}")
    for tag, (v, _, d) in res.items():
        if v in ("WRONG", "HARNESS"):
            print(f"  [{v}] {tag}: {d}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--synth", default=os.environ.get("SYNTH", "./target/debug/synth"))
    ap.add_argument("--before")
    ap.add_argument("--after")
    ap.add_argument("--json")
    ap.add_argument("--expect", help="exact counts: ok=,refused=,wrong=,guard=")
    args = ap.parse_args()
    n = len(cells())
    if n != POPULATION:
        print(f"POPULATION {n} != {POPULATION}: the matrix axes moved")
        return 1
    if args.before or args.after:
        if not (args.before and args.after):
            ap.error("--before and --after go together")
        b, a = run_matrix(args.before), run_matrix(args.after)
        show(f"before {args.before}", b)
        show(f"after  {args.after}", a)
        tr = Counter((b[t][0], a[t][0]) for t in b)
        print("=== transitions (before -> after) ===")
        for (x, y), k in sorted(tr.items()):
            print(f"  {x:>8} -> {y:<8} {k}")
        if args.json:
            Path(args.json).write_text(json.dumps(
                {"before": b, "after": a}, indent=0, sort_keys=True))
        return 0
    res = run_matrix(args.synth)
    show(args.synth, res)
    if args.json:
        Path(args.json).write_text(json.dumps(res, indent=0, sort_keys=True))
    c, why, _ = summary(res)
    measured = {"ok": c["ok"], "refused": c["REFUSED"], "wrong": c["WRONG"],
                "guard": why["npa-guard"]}
    bad = c["WRONG"] + c["HARNESS"]
    if args.expect:
        for kv in args.expect.split(","):
            k, v = kv.split("=")
            if measured[k] != int(v):
                print(f"EXPECT {k}={v}, measured {measured[k]}")
                bad += 1
    print(f"ORACLE: {'PASS' if bad == 0 else 'FAIL'}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
