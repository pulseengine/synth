#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 2201
"""RQ-91-MPUENFORCE (#1145) — the `--emit-memory-facts` sidecar is SUFFICIENT
for every legitimate access, checked by EXECUTION, and exact against the
hand-written per-function tables the multi-memory oracles already carry.

WHAT THE FACTS ARE FOR. gale programs the MPU itself (its verified
`switch_to_partition`, the only MPU writer; synth emits none). Its build-time
gate proves each domain's grant is SUFFICIENT (no legitimate access faults)
and MINIMAL from the sidecar's per-function memory sets. A set that misses a
memory a function really touches is a fault on silicon in a correct program;
a set wider than needed is an over-grant. This oracle checks the first by
execution and the second against independent tables.

HOW. Every fixture is compiled with `--emit-memory-facts`, every section is
hand-linked at its own NON-ADJACENT base with the gaps unmapped, and every
data access is hooked with its PC and attributed to the `func_N` body whose
symbol range holds that PC. A call counts only when wasmtime does NOT trap on
it (a legitimate access; an out-of-bounds address can land anywhere and is
not what a grant is for), and its result must equal wasmtime's. Then:
  SUFFICIENCY   every access to memory k by func_N has k in func_N's
                `direct_memories`, and in the called export's `memories`.
  EXACTNESS     where the source oracle carries a hand-written table
                (#1145 bulk/adapter, #1145 NPA, #1622 i64), the sidecar's set
                equals it: per function for the bulk and #1622 tables
                (direct), per export for the NPA call table (transitive).
  NON-VACUITY   every memory of every fixture is observed accessed, and the
                observed set of each export equals its `memories` unless the
                widening is a stated `via_call_indirect`.
  POTENCY       the sufficiency check is re-run against a MUTATED sidecar
                (one observed memory removed from one function) and must red.
  BYTES         the object compiled with the flag is byte-identical to the one
                compiled without it, and the sidecar's `object_sha256` is that
                object's sha256.
  BOUNDS        every memory's `size_bytes` / `pmsav7_region_bytes` /
                `section_align` / `section_bytes` equal the object's own
                `__synth_mem_size_k`, `__synth_mem_region_k` and section
                header, read here with pyelftools (a second reader).
  LAYOUT        `--mpu-layout pmsav7` pads `.synth.wasm_mem_k` to its region
                and `pmsav7-srd` to the subregion granule, alignment unchanged,
                execution still equal to wasmtime, and without the flag the
                v0.68 section shape is unchanged.
  REFUSALS      a single-memory module, a partial or overlapping domain map,
                a domain map without the facts flag, a non-relocatable
                compile, and --mpu-layout on one memory, an imported memory
                or an unknown layout each refuse, by name.
  DOMAINS       with `--memory-domain`, both readings are pinned with their
                roles: `direct_spans_domains` (the supervisor-only assertion)
                and `spans_domains` (the boundary census, where the tenant's
                own entry reaching supervisor memory is a TRUE finding).
  EDGES         `cross_domain_edges` lists exactly the one known crossing of
                the adapter fixture (tenant_call's `call $adapter`), its site
                checked against the wasm bytes (a `call 2` at that offset);
                every EXECUTED call whose callee reaches beyond the caller's
                domains is a listed edge; cutting the listed edges leaves every
                function's reach inside its `sits_in_domains` (gale's gate);
                and dropping any listed edge reds that cut check.

Fixtures are IMPORTED from the oracles that own them, so a fixture change
there is a change here: multi_memory_bulk_1145_differential (adapter, bulk3),
npa_multi_memory_1145_differential (pages, pagesize1, two_sp, launder01,
two_sp_npa, xcopy_merge), memk_bulk_oob_1619_differential (the three-memory
bulk/load/store module, in-bounds calls) and memk_i64_1622_differential (the
gale-sized and paged i64 fixtures); plus the #1145 two-tenant and the #406
modules from their .wat files.

RED-FIRST: on main eab66646 the flag does not exist, so every compile here
fails and the oracle FAILS.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/memory_facts_1145_differential.py
"""

import copy
import hashlib
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (UC_ARCH_ARM, UC_HOOK_BLOCK, UC_HOOK_MEM_READ,
                     UC_HOOK_MEM_WRITE, UC_MODE_THUMB, Uc, UcError)
from unicorn.arm_const import (UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0,
                               UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                               UC_ARM_REG_R4, UC_ARM_REG_R9, UC_ARM_REG_R10,
                               UC_ARM_REG_R11, UC_ARM_REG_R12, UC_ARM_REG_SP)

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import memk_bulk_oob_1619_differential as k1619  # noqa: E402
import memk_i64_1622_differential as k1622  # noqa: E402
import multi_memory_bulk_1145_differential as mmb  # noqa: E402
import npa_multi_memory_1145_differential as npa  # noqa: E402

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
R_ARM_ABS32, R_ARM_THM_CALL = 2, 10
TEXT, BSS, DATA = 0x0010_0000, 0x0040_0000, 0x0080_0000
MEMK = 0x0100_0000            # memory k at MEMK + (k-1) * MEMK_STRIDE
MEMK_STRIDE = 0x0080_0000
STACK_BASE, STACK_SIZE = 0x0400_0000, 0x1_0000
GLOBALS_BASE = 0x0500_0000
GARBAGE = 0xDEADBEEF
MODES = {
    "plain": ["--embedder-data-init", "--embedder-global-init"],
    "npa": ["--native-pointer-abi"],
    "software": ["--embedder-data-init", "--embedder-global-init",
                 "--safety-bounds", "software"],
    # gale's own invocation: the embedder programs the MPU.
    "mpu": ["--embedder-data-init", "--embedder-global-init",
            "--safety-bounds", "mpu", "--embedder-mpu"],
}


def rup(n):
    return max(0x1000, (n + 0xFFF) & ~0xFFF)


def thm_bl(src, dst):
    off = dst - (src + 4)
    imm = (off >> 1) & 0xFFFFFF
    s, i1, i2 = (imm >> 23) & 1, (imm >> 22) & 1, (imm >> 21) & 1
    j1, j2 = (~(i1 ^ s)) & 1, (~(i2 ^ s)) & 1
    return struct.pack("<HH", 0xF000 | (s << 10) | ((imm >> 11) & 0x3FF),
                       0xD000 | (j1 << 13) | (j2 << 11) | (imm & 0x7FF))


def compile_obj(wat, tmp, label, flags, facts=True):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}{'' if facts else '.nofacts'}.o"
    side = Path(str(obj) + ".memfacts.json")
    for p in (obj, side):
        if p.exists():
            p.unlink()
    cmd = [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m3",
           "--all-exports", "--relocatable", *flags]
    if facts:
        cmd.append("--emit-memory-facts")
    r = subprocess.run(cmd, capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    return r.returncode, (r.stdout or "") + (r.stderr or ""), obj, side


class Linked:
    """The harness is the embedder: every section at its own base."""

    def __init__(self, obj, mode, wat):
        self.npa = mode == "npa"
        e = ELFFile(open(obj, "rb"))
        secs = list(e.iter_sections())
        self.bases = {".text": TEXT, ".bss": BSS, ".data": DATA}
        for s in secs:
            if s.name.startswith(".synth.wasm_mem_"):
                k = int(s.name.rsplit("_", 1)[1])
                self.bases[s.name] = MEMK + (k - 1) * MEMK_STRIDE
        self.sizes, self.align, blobs = {}, {}, {}
        for s in secs:
            if s.name in self.bases:
                self.sizes[s.name] = s["sh_size"]
                self.align[s.name] = s["sh_addralign"]
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
                if sec in self.bases:
                    self.syms[s.name] = (sec, s["st_value"], s["st_size"])
                    if (sec == ".text" and s["st_size"] and s.name.startswith("func_")
                            and s["st_info"]["type"] == "STT_FUNC"):
                        lo = TEXT + (s["st_value"] & ~1)
                        self.funcs.append((lo, lo + s["st_size"], s.name))
        self.nmem = self.abs["__synth_mem_count"]
        self.msize = [self.abs[f"__synth_mem_size_{k}"] for k in range(self.nmem)]
        if not self.npa or ".bss" not in self.sizes:
            self.sizes[".bss"] = self.msize[0]
            blobs[".bss"] = b""
            self.syms["__synth_wasm_data"] = (".bss", 0, 0)
        text = bytearray(blobs[".text"])
        rel = e.get_section_by_name(".rel.text")
        for r in (rel.iter_relocations() if rel else []):
            sym = symtab.get_symbol(r["r_info_sym"])
            if sym["st_shndx"] == "SHN_ABS":
                dst = sym["st_value"]
            elif sym.name in self.syms:
                dst = self.addr(sym.name)
            else:
                raise SystemExit(f"unresolvable reloc target {sym.name!r}")
            if r["r_info_type"] == R_ARM_ABS32:
                (add,) = struct.unpack_from("<I", text, r["r_offset"])
                struct.pack_into("<I", text, r["r_offset"], (dst + add) & 0xFFFFFFFF)
            elif r["r_info_type"] == R_ARM_THM_CALL:
                text[r["r_offset"]:r["r_offset"] + 4] = thm_bl(TEXT + r["r_offset"], dst & ~1)
            else:
                raise SystemExit(f"unhandled reloc type {r['r_info_type']}")
        self.text = bytes(text)
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for name, base in self.bases.items():
            self.mu.mem_map(base, rup(self.sizes.get(name, 0) + 0x20))
        self.mu.mem_map(STACK_BASE, STACK_SIZE)
        self.mu.mem_map(GLOBALS_BASE, 0x1000)
        self.ret = TEXT + rup(len(text) + 0x20) - 0x10
        self.mu.mem_write(TEXT, self.text)
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")
        for name, blob in blobs.items():
            if blob and name != ".text":
                self.mu.mem_write(self.bases[name], blob)
        if not self.npa:
            for off, b in segments0(wat):
                self.mu.mem_write(BSS + off, b)
            for i, v in enumerate(mmb.global_inits(wat)):
                self.mu.mem_write(GLOBALS_BASE + 4 * i, struct.pack("<I", v))
        self.segs0 = segments0(wat)
        self.seg_syms = sorted(
            (int(n[len("__synth_wasm_seg_"):]), self.addr(n))
            for n in self.syms if n.startswith("__synth_wasm_seg_"))
        self.accesses = []
        self.transitions = []
        self.entry_of = {lo: name for lo, _, name in self.funcs}
        self.mu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, self._hook)
        self.mu.hook_add(UC_HOOK_BLOCK, self._block)

    def _hook(self, uc, acc, addr, size, val, ud):
        self.accesses.append((uc.reg_read(UC_ARM_REG_PC), addr))

    def _block(self, uc, addr, size, ud):
        """A block starting at a func_N entry is a call into it: record
        (caller body, callee) from the link register."""
        callee = self.entry_of.get(addr & ~1)
        if callee is None:
            return
        lr = uc.reg_read(UC_ARM_REG_LR) & ~1
        caller = self.func_of(lr - 2)
        if caller.startswith("func_"):
            self.transitions.append((caller, callee))

    def addr(self, name):
        sec, val, _ = self.syms[name]
        return self.bases[sec] + val

    def mem_of(self, a):
        """The wasm memory an address belongs to, or a non-memory label."""
        for name, base in self.bases.items():
            if base <= a < base + max(self.sizes.get(name, 0), 1):
                if name == ".text":
                    return "text"
                if name == ".data":
                    g = self.syms.get("__synth_globals")
                    if g and a >= self.addr("__synth_globals"):
                        return "globals"
                    return 0
                if name == ".bss":
                    return 0
                return int(name.rsplit("_", 1)[1])
        if STACK_BASE <= a < STACK_BASE + STACK_SIZE:
            return "stack"
        if GLOBALS_BASE <= a < GLOBALS_BASE + 0x1000:
            return "globals"
        return f"OUTSIDE@{a:#x}"

    def func_of(self, pc):
        for lo, hi, name in self.funcs:
            if lo <= pc < hi:
                return name
        return f"pc@{pc:#x}"

    def native0(self, off):
        if not self.npa:
            return off
        for k2, a in reversed(self.seg_syms):
            soff, b = self.segs0[k2]
            if soff <= off < soff + len(b):
                return a + (off - soff)
        return self.addr("__synth_wasm_data") + off

    def call(self, fn, args):
        regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
        for i, r in enumerate(regs):
            self.mu.reg_write(r, GARBAGE ^ i)
        for i in range(5):
            self.mu.reg_write(UC_ARM_REG_R4 + i, GARBAGE ^ (0x100 * i))
        slot = 0
        for a in args:
            if isinstance(a, tuple):  # ("i64", v): an even register pair (#518)
                slot += slot & 1
                self.mu.reg_write(regs[slot], a[1] & 0xFFFFFFFF)
                self.mu.reg_write(regs[slot + 1], (a[1] >> 32) & 0xFFFFFFFF)
                slot += 2
                continue
            if isinstance(a, str):
                a = self.native0(int(a[2:], 16))
            self.mu.reg_write(regs[slot], a & 0xFFFFFFFF)
            slot += 1
        self.mu.reg_write(UC_ARM_REG_R12, GARBAGE)
        self.mu.reg_write(UC_ARM_REG_R9, GARBAGE if self.npa else GLOBALS_BASE)
        self.mu.reg_write(UC_ARM_REG_R11, 0 if self.npa else BSS)
        self.mu.reg_write(UC_ARM_REG_R10, self.msize[0])
        self.mu.reg_write(UC_ARM_REG_SP, STACK_BASE + STACK_SIZE - 0x100)
        self.mu.reg_write(UC_ARM_REG_LR, self.ret | 1)
        self.accesses = []
        self.transitions = []
        try:
            self.mu.emu_start(self.addr(fn) | 1, self.ret, timeout=20_000_000)
        except UcError as ex:
            return f"FAULT {ex}"
        return (self.mu.reg_read(UC_ARM_REG_R1) << 32) | self.mu.reg_read(UC_ARM_REG_R0)


def segments0(wat):
    """Memory 0's active segments, whatever the memory is named."""
    m0 = re.search(r"\(memory \$(\w+) \d", wat).group(1)
    out = []
    for m in re.finditer(r'\(data (?:\$\w+ )?\(memory \$' + m0
                         + r'\) \(i32\.const (0x[0-9a-fA-F]+|\d+)\) "([^"]*)"\)', wat):
        out.append((int(m.group(1), 0), mmb.wat_bytes(m.group(2))))
    return out


def norm_args(args):
    """Every source oracle's argument spelling -> ints, `n:` strings and
    ("i64", v) tuples."""
    out = []
    for a in args:
        if isinstance(a, tuple):
            kind, v = a
            if kind == "i64":
                out.append(("i64", v))
            elif kind == "n0":
                out.append(f"n:{v:#x}")
            else:
                out.append(v)
        elif isinstance(a, int) and a > 0xFFFFFFFF:
            out.append(("i64", a))  # the #1619 spelling of an i64 argument
        else:
            out.append(a)
    return out


def wasm_arg(a):
    if isinstance(a, tuple):
        v = a[1]
        return v - (1 << 64) if v >= (1 << 63) else v
    if isinstance(a, str):
        return int(a[2:], 16)
    return a - (1 << 32) if a >= (1 << 31) else a


def wasmtime_instance(wat):
    """The reference. Memory contents are not compared here (the source
    oracles do that); the memory count is the number of declarations."""
    nmem = len(re.findall(r"\(memory \$\w+ \d", wat))
    cfg = wasmtime.Config()
    cfg.wasm_multi_memory = True
    cfg.wasm_custom_page_sizes = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    return st, wasmtime.Instance(st, wasmtime.Module(eng, wat), []).exports(st), nmem


def facts_by_symbol(doc):
    by = {f["symbol"]: f for f in doc["functions"]}
    for f in doc["functions"]:
        if f["export"]:
            by[f["export"]] = f
    return by


def check_accesses(ln, facts, export, accesses):
    """SUFFICIENCY over one call. Returns (breaches, observed per symbol)."""
    by = facts_by_symbol(facts)
    breaches, seen = [], {}
    for pc, a in accesses:
        m = ln.mem_of(a)
        if isinstance(m, str):
            if m.startswith("OUTSIDE"):
                breaches.append(f"{ln.func_of(pc)}:{m}")
            continue
        f = ln.func_of(pc)
        seen.setdefault(f, set()).add(m)
        if f not in by:
            breaches.append(f"{f}:no-facts")
        elif m not in by[f]["direct_memories"]:
            breaches.append(f"{f}:m{m}-not-in-direct{by[f]['direct_memories']}")
        if m not in by[export]["memories"]:
            breaches.append(f"{export}:m{m}-not-in-memories{by[export]['memories']}")
    return breaches, seen


def cut_violations(doc, edges=None):
    """gale's gate, over the sidecar alone: with the listed crossings cut,
    the domains a function reaches through its call tree must lie inside the
    domains it sits in. Returns the violations (empty when the edges are
    complete)."""
    edges = doc["cross_domain_edges"] if edges is None else edges
    cut = {(e["caller"], e["callee"]) for e in edges}
    dom_of = {k: d for d, ks in doc["domains"].items() for k in ks}
    alld = set(doc["domains"])
    sym = {f["symbol"]: f for f in doc["functions"]}
    bad = []
    for f in doc["functions"]:
        seen, stack, reach = set(), [f["symbol"]], set()
        while stack:
            s = stack.pop()
            if s in seen:
                continue
            seen.add(s)
            g = sym[s]
            reach |= {dom_of[k] for k in g["direct_memories"]}
            if g["direct_call_indirect"] and (s, "call_indirect") not in cut:
                reach |= alld  # an uncut call_indirect in this body reaches every domain
            for c in g["direct_calls"]:
                if c in sym and (s, c) not in cut:
                    stack.append(c)
        if not reach <= set(f["sits_in_domains"]):
            bad.append(f"{f['symbol']} reaches {sorted(reach)} but sits in "
                       f"{f['sits_in_domains']}")
    return bad


class Tally:
    def __init__(self):
        self.calls = self.accesses = self.fails = self.edge_checks = 0
        self.mem_seen = set()

    def bad(self, msg):
        self.fails += 1
        print(f"  [BUG] {msg}")


def check_bounds(ln, doc, label, t):
    for m in doc["memories"]:
        k = m["index"]
        want = (ln.abs[f"__synth_mem_size_{k}"], ln.abs[f"__synth_mem_region_{k}"])
        got = (m["size_bytes"], m["pmsav7_region_bytes"])
        if got != want:
            t.bad(f"{label}: memory {k} bounds {got} != object {want}")
        if k > 0:
            sec = f".synth.wasm_mem_{k}"
            if (m["section_align"], m["section_bytes"]) != (ln.align[sec], ln.sizes[sec]):
                t.bad(f"{label}: memory {k} section facts != section header")
            if m["base"] != {"kind": "symbol", "symbol": f"__synth_mem_base_{k}",
                             "section": sec}:
                t.bad(f"{label}: memory {k} base {m['base']}")
        elif m["base"]["kind"] != ("native" if ln.npa else "register"):
            t.bad(f"{label}: memory 0 base {m['base']}")


def run_fixture(label, wat, calls, mode, tmp, t, hand=None, hand_kind=None,
                extra=(), potency=False):
    flags = MODES[mode] + list(extra)
    rc, log, obj, side = compile_obj(wat, tmp, f"{label}.{mode}", flags)
    if rc != 0 or not side.exists():
        tail = [ln for ln in log.splitlines() if "rror" in ln][:2]
        t.bad(f"{label}/{mode}: compile rc={rc} sidecar={side.exists()}: {' | '.join(tail)[:300]}")
        return
    plain_flags = []  # the same compile without the facts flags
    it = iter(flags)
    for f in it:
        if f == "--memory-domain":
            next(it)
        else:
            plain_flags.append(f)
    rc2, _, obj2, _ = compile_obj(wat, tmp, f"{label}.{mode}", plain_flags, facts=False)
    data = obj.read_bytes()
    doc = json.loads(side.read_text())
    if rc2 != 0 or obj2.read_bytes() != data:
        t.bad(f"{label}/{mode}: object differs with --emit-memory-facts")
    if doc["object_sha256"] != hashlib.sha256(data).hexdigest():
        t.bad(f"{label}/{mode}: object_sha256 is not the object's")
    if doc["schema"] != "synth-memfacts-v1":
        t.bad(f"{label}/{mode}: schema {doc['schema']}")
    ln = Linked(obj, mode, wat)
    check_bounds(ln, doc, f"{label}/{mode}", t)
    by = facts_by_symbol(doc)
    st, ex, nmem = wasmtime_instance(wat)
    observed_export = {}
    observed_func = {}
    kept = []
    transitions = set()
    for fn, args in calls:
        args = norm_args(args)
        try:
            res = ex[fn](st, *[wasm_arg(a) for a in args])
        except wasmtime.Trap:
            continue  # not a legitimate access: no grant is owed for it
        got = ln.call(fn, args)
        t.calls += 1
        if isinstance(got, str):
            t.bad(f"{label}/{mode}.{fn}{tuple(args)} -> {got} (wasmtime returned)")
            continue
        if res is not None:
            wide = str(ex[fn].type(st).results[0]) == "i64"
            mask = 0xFFFFFFFFFFFFFFFF if wide else 0xFFFFFFFF
            if (got & mask) != (res & mask):
                t.bad(f"{label}/{mode}.{fn}{tuple(args)} -> {got & mask:#x}, "
                      f"wasmtime {res & mask:#x}")
        breaches, seen = check_accesses(ln, doc, fn, ln.accesses)
        t.accesses += sum(len(v) for v in seen.values())
        for b in sorted(set(breaches))[:4]:
            t.bad(f"{label}/{mode}.{fn}{tuple(args)} ISOLATION {b}")
        for f, ms in seen.items():
            observed_func.setdefault(f, set()).update(ms)
            observed_export.setdefault(fn, set()).update(ms)
            t.mem_seen.update((label, m) for m in ms)
        kept.append((fn, args, list(ln.accesses)))
        transitions.update(ln.transitions)
    # NON-VACUITY: every memory some function's facts say is accessed is
    # observed accessed.
    for k in sorted({k for f in doc["functions"] for k in f["direct_memories"]}):
        if (label, k) not in t.mem_seen:
            t.bad(f"{label}/{mode}: memory {k} never accessed — vacuous")
    # MINIMALITY on the observed calls: an export's memories, unless widened
    # by a stated call_indirect, are exactly what its calls touched.
    for fn, ms in observed_export.items():
        f = by[fn]
        if not f["via_call_indirect"] and set(f["memories"]) != ms:
            t.bad(f"{label}/{mode}.{fn}: MINIMALITY — memories {f['memories']} but the "
                  f"calls touched {sorted(ms)}")
    for f, ms in observed_func.items():
        if set(by[f]["direct_memories"]) != ms:
            print(f"  [note] {label}/{mode}.{f}: direct {by[f]['direct_memories']} "
                  f"observed {sorted(ms)} (a body not every path of which ran)")
    # EXACTNESS against the source oracle's own table.
    if hand:
        for name, want in hand.items():
            f = by.get(name)
            if f is None:
                t.bad(f"{label}: hand-table function {name} has no facts")
                continue
            key = "memories" if hand_kind == "export" else "direct_memories"
            if set(f[key]) != set(want):
                t.bad(f"{label}/{mode}: {name}.{key} {f[key]} != table {sorted(want)}")
    # POTENCY: a mutated sidecar must red on the recorded accesses.
    if potency:
        for f, ms in observed_func.items():
            m = min(ms)
            mut = copy.deepcopy(doc)
            for g in mut["functions"]:
                if g["symbol"] == f:
                    g["direct_memories"] = [x for x in g["direct_memories"] if x != m]
            red = any(check_accesses(ln, mut, fn, acc)[0] for fn, _, acc in kept)
            if not red:
                t.bad(f"{label}/{mode}: POTENCY — removing m{m} from {f} stayed green")
            else:
                print(f"  [ok ] potency: removing m{m} from {f} reds")
            break
    # EDGES: every executed call whose callee's reach leaves the caller's
    # domains is a listed crossing, and cutting the listed crossings leaves
    # every function's reach inside the domains it sits in.
    if doc["domains"]:
        pairs = {(e["caller"], e["callee"]) for e in doc["cross_domain_edges"]}
        sym = {f["symbol"]: f for f in doc["functions"]}
        for f, g in sorted(transitions):
            if not set(sym[g]["domains"]) <= set(sym[f]["sits_in_domains"]) and (f, g) not in pairs:
                t.bad(f"{label}/{mode}: executed crossing {f} -> {g} is not a listed edge")
        t.edge_checks += len(transitions)
        for v in cut_violations(doc):
            t.bad(f"{label}/{mode}: cut check — {v}")
    print(f"  [{'ok ' if t.fails == 0 else '...'}] {label}/{mode}: {len(kept)} calls")
    return doc


def two_tenant_calls():
    return ([("read_a", [i]) for i in range(7)] + [("read_b", [i]) for i in range(7)]
            + [("write_a", [3, 0x5A]), ("read_a", [3]), ("read_b", [3])])


def mem406_calls():
    return [("store_both_read0", [0x40, 0x11, 0x22]), ("store_both_read1", [0x44, 0x33, 0x44])]


def layout_legs(tmp, t):
    wat = (HERE / "mem406_multi_memory.wat").read_text()
    for layout, want_bytes in (("pmsav7", 1 << 18), ("pmsav7-srd", 3 * 65536)):
        label = f"mem406.{layout}"
        run_fixture(label, wat, mem406_calls(), "plain", tmp, t,
                    extra=["--mpu-layout", layout])
        rc, log, obj, side = compile_obj(wat, tmp, f"{label}.plain", MODES["plain"]
                                         + ["--mpu-layout", layout])
        if rc != 0 or not side.exists():
            t.bad(f"{label}: compile rc={rc}")
            continue
        s = ELFFile(open(obj, "rb")).get_section_by_name(".synth.wasm_mem_1")
        if (s["sh_addralign"], s["sh_size"]) != (1 << 18, want_bytes):
            t.bad(f"{label}: section align/size {s['sh_addralign']}/{s['sh_size']}")
        doc = json.loads(side.read_text())
        m1 = doc["memories"][1]
        sub = 6 if layout == "pmsav7-srd" else None
        if (m1["section_bytes"], m1["pmsav7_subregions_enabled"], doc["mpu_layout"]) != (
                want_bytes, sub, layout):
            t.bad(f"{label}: facts {m1['section_bytes']} {m1['pmsav7_subregions_enabled']}")
        else:
            print(f"  [ok ] {label}: .synth.wasm_mem_1 align {1 << 18:#x} size {want_bytes:#x}")
    # The layout moves only the padded section: without it, the v0.68 shape.
    rc, _, obj, _ = compile_obj(wat, tmp, "mem406.nolayout", MODES["plain"])
    if rc != 0:
        t.bad(f"mem406 without --mpu-layout: compile rc={rc}")
        return
    s = ELFFile(open(obj, "rb")).get_section_by_name(".synth.wasm_mem_1")
    if (s["sh_addralign"], s["sh_size"]) != (1 << 18, 3 * 65536):
        t.bad("mem406 without --mpu-layout: v0.68 section shape moved")


REFUSALS = [
    ("layout-one-memory", "(module (memory 1) (func (export \"f\") (result i32) "
     "(i32.load (i32.const 0))))", ["--mpu-layout", "pmsav7"], "--mpu-layout (#1145)"),
    ("layout-imported", "(module (import \"env\" \"m\" (memory 1 1)) (memory $b 1 1) "
     "(func (export \"f\") (result i32) (i32.load $b (i32.const 0))))",
     ["--mpu-layout", "pmsav7"], "imports 1 linear memory"),
    ("layout-unknown", "(module (memory $a 1) (memory $b 1))",
     ["--mpu-layout", "pmsav8"], "--mpu-layout \"pmsav8\""),
    # (label, wat, flags, needle)
    ("facts-one-memory", "(module (memory 1) (func (export \"f\") (result i32) "
     "(i32.load (i32.const 0))))", ["--emit-memory-facts"], "carries no region table"),
    ("domain-partial", "(module (memory $a 1) (memory $b 1) (func (export \"f\") "
     "(result i32) (i32.load $b (i32.const 0))))",
     ["--emit-memory-facts", "--memory-domain", "t=0"], "belong to no domain"),
    ("domain-overlap", "(module (memory $a 1) (memory $b 1) (func (export \"f\") "
     "(result i32) (i32.load $b (i32.const 0))))",
     ["--emit-memory-facts", "--memory-domain", "t=0,1", "--memory-domain", "s=1"],
     "claimed by both"),
    ("domain-without-facts", "(module (memory $a 1) (memory $b 1))",
     ["--memory-domain", "t=0,1"], "without --emit-memory-facts"),
    # An imported memory 0 beside a defined memory 1 does not compile today
    # (the memory-1 access declines: "the module context declares 1
    # memories", #406), so no sidecar ever carries
    # `imported: true`; pinned so the day it compiles this leg moves.
    ("facts-imported-plus-defined", "(module (import \"env\" \"mem\" (memory 1 1)) "
     "(memory $b 1 1) (func (export \"r1\") (param i32) (result i32) "
     "(i32.load8_u $b (local.get 0))))", ["--embedder-data-init", "--emit-memory-facts"],
     "module context declares 1 memories"),
]


def refusal_legs(tmp, t):
    for label, wat, flags, needle in REFUSALS:
        src = tmp / f"{label}.wat"
        src.write_text(wat)
        r = subprocess.run([SYNTH, "compile", str(src), "-o", str(tmp / f"{label}.o"),
                            "--target", "cortex-m3", "--all-exports", "--relocatable",
                            *flags], capture_output=True, text=True,
                           env={"PATH": "/usr/bin:/bin"})
        out = (r.stdout or "") + (r.stderr or "")
        if r.returncode == 0 or needle not in out:
            t.bad(f"refusal {label}: rc={r.returncode}, needle {needle!r} missing")
        else:
            print(f"  [ok ] refusal {label}")
    src = tmp / "not-reloc.wat"
    src.write_text("(module (memory $a 1) (memory $b 1))")
    r = subprocess.run([SYNTH, "compile", str(src), "-o", str(tmp / "nr.elf"), "--target",
                        "cortex-m3", "--all-exports", "--emit-memory-facts"],
                       capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    if r.returncode == 0 or "ARM `--relocatable` object only" not in r.stderr + r.stdout:
        t.bad("refusal not-relocatable")
    else:
        print("  [ok ] refusal not-relocatable")


def domain_leg(tmp, t):
    doms = ["--memory-domain", "tenant=0", "--memory-domain", "supervisor=1"]
    doc = run_fixture("adapter.domains", mmb.ADAPTER, mmb.ADAPTER_CALLS, "plain", tmp, t,
                      extra=doms)
    if doc is None:
        return
    name = {0: "tenant", 1: "supervisor"}
    for f in doc["functions"]:
        for key, mems in (("", f["memories"]), ("direct_", f["direct_memories"])):
            ds = {name[k] for k in mems}
            if (f[key + "spans_domains"] != (len(ds) > 1)
                    or set(f[key + "domains"]) != ds):
                t.bad(f"domains: {f['symbol']} {key}spans/domains disagree with {mems}")
    # Both readings, pinned, each with its role. The transitive one is the
    # boundary census: the tenant's own entry reaching supervisor memory is
    # a TRUE finding. The direct one is the supervisor-only assertion.
    for key, want in (("spans_domains", ["copy01", "copy10", "copy_static", "func_2",
                                         "tenant_call"]),
                      ("direct_spans_domains", ["copy01", "copy10", "copy_static",
                                                "func_2"])):
        got = sorted(f["export"] or f["symbol"] for f in doc["functions"] if f[key])
        if got != want:
            t.bad(f"domains: {key} {got} != {want}")
        else:
            print(f"  [ok ] domains: {key} {got}")
    for key in ("spans_domains", "direct_spans_domains", "cross_domain_edges"):
        if key not in doc["field_roles"]:
            t.bad(f"domains: field_roles has no role for {key}")
    calls = {f["export"] or f["symbol"]: f["direct_calls"] for f in doc["functions"]}
    if calls["tenant_call"] != ["func_2"] or calls["func_2"] != ["func_0", "func_1"]:
        t.bad(f"domains: call edges {calls['tenant_call']} / {calls['func_2']}")
    # The ONE known crossing: tenant_call's `call $adapter`.
    edges = doc["cross_domain_edges"]
    want = [("direct", "func_3", "tenant_call", "func_2", ["tenant"], ["supervisor", "tenant"])]
    got = [(e["kind"], e["caller"], e["caller_export"], e["callee"], e["caller_domains"],
            e["callee_domains"]) for e in edges]
    if got != want:
        t.bad(f"domains: cross_domain_edges {got} != {want}")
    else:
        # The site, checked against the wasm bytes independently of synth's
        # decoder: a `call` (0x10) of function 2 at that module offset.
        wasm = wasmtime.wat2wasm(mmb.ADAPTER)
        off = edges[0]["site"]["wasm_offset"]
        ok = (off is not None and edges[0]["site"]["function_index"] == 3
              and wasm[off] == 0x10 and wasm[off + 1] == 0x02)
        if not ok:
            t.bad(f"domains: edge site {edges[0]['site']} is not `call 2` in the wasm")
        else:
            print(f"  [ok ] domains: exactly one crossing, tenant_call -> func_2 "
                  f"(func 3, op {edges[0]['site']['op_index']}, wasm offset {off:#x})")
    # POTENCY: drop each listed edge; the cut check must red.
    for i in range(len(edges)):
        rest = edges[:i] + edges[i + 1:]
        if not cut_violations(doc, rest):
            t.bad(f"domains: POTENCY — dropping edge {i} left the cut check green")
        else:
            print(f"  [ok ] potency: dropping edge {edges[i]['caller']} -> "
                  f"{edges[i]['callee']} reds the cut check")


def main():
    tmp = Path(tempfile.mkdtemp(prefix="memfacts_1145_"))
    t = Tally()
    print("=== #1145 two-tenant, #406 ===")
    tt = (HERE / "mem_isolation_two_tenant_1145.wat").read_text()
    # (no npa leg: its memory-0 data segment has no memory-0 static
    # reference, which --native-pointer-abi refuses on its own)
    for mode in ("plain", "software", "mpu"):
        run_fixture("two_tenant", tt, two_tenant_calls(), mode, tmp, t,
                    hand={"read_a": {0}, "read_b": {1}, "write_a": {0}},
                    potency=(mode == "plain"))
    m406 = (HERE / "mem406_multi_memory.wat").read_text()
    run_fixture("mem406", m406, mem406_calls(), "plain", tmp, t)
    print("=== #1145 bulk (multi_memory_bulk_1145_differential) ===")
    for label, wat, funcs, calls in mmb.FIXTURES:
        for mode in ("plain", "npa"):
            run_fixture(label, wat, calls, mode, tmp, t, hand=funcs, hand_kind="direct",
                        potency=True)
    print("=== #1145 NPA (npa_multi_memory_1145_differential) ===")
    for label, wat, calls in npa.FIXTURES:
        hand = {}
        for fn, _, ms in calls:
            hand.setdefault(fn, set()).update(ms)
        run_fixture(label, wat, [(fn, a) for fn, a, _ in calls], "npa", tmp, t,
                    hand=hand, hand_kind="export")
    hand = {}
    for fn, _, ms in npa.XCOPY_MERGE_CALLS:
        hand.setdefault(fn, set()).update(ms)
    run_fixture("xcopy_merge", npa.XCOPY_MERGE, [(fn, a) for fn, a, _ in npa.XCOPY_MERGE_CALLS],
                "npa", tmp, t, hand=hand, hand_kind="export", extra=[npa.FLAG])
    print("=== #1619 (memk_bulk_oob_1619_differential) ===")
    inb = [(fn, a) for fn, a, ok in k1619.XCALLS if ok]
    for mode in ("plain", "software"):
        run_fixture("k1619", k1619.XMOD, inb, mode, tmp, t)
    run_fixture("k1619", k1619.KMOD, [(fn, a) for fn, a, ok in k1619.KCALLS if ok],
                "npa", tmp, t)
    print("=== #1622 (memk_i64_1622_differential) ===")
    for label, mem0, mem1, extent, minimal in k1622.FIXTURES:
        wat, funcs, calls = k1622.build_fixture(mem0, mem1, extent, minimal)
        for mode in ("plain", "npa"):
            run_fixture(f"k1622-{label}", wat, [(fn, a) for fn, a, _ in calls], mode, tmp, t,
                        hand=funcs, hand_kind="direct")
    print("=== --mpu-layout ===")
    layout_legs(tmp, t)
    print("=== refusals ===")
    refusal_legs(tmp, t)
    print("=== --memory-domain ===")
    domain_leg(tmp, t)
    print(f"\nlegitimate calls: {t.calls}, attributed memory accesses: {t.accesses}, "
          f"executed call transitions checked against the edges: {t.edge_checks}")
    if t.calls < 2201:
        print(f"VACUOUS: {t.calls} calls")
        return 1
    print(f"ORACLE: {'PASS' if t.fails == 0 else f'FAIL ({t.fails})'}")
    return 0 if t.fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
