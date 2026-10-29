#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 51
"""RQ-89-MEMLAYER6 (#1145) — `--native-pointer-abi` on a MULTI-MEMORY ARM
`--relocatable` module, layered per memory — execution differential vs
wasmtime (multi-memory + custom-page-sizes enabled), with an isolation check.

THE ABI UNDER TEST. Memory 0 is native (R11 = 0; a static at wasm offset C
lives at `__synth_wasm_data + C`, retargeted to `__synth_wasm_seg_K` on the
mixed split; the stack-pointer global is rebased on read). Memory k > 0 is a
wasm OFFSET addressed through its own `__synth_wasm_data_<k>` region — the
non-NPA multi-memory lowering, unchanged. The CLI's module-level provenance
pass (`synth_core::npa_multi_memory`) keeps every constant inside memory 0's
static window that reaches a memory-k address RAW, refuses one that reaches
both memories, and picks memory 0's stack pointer among the globals that
never reach memory k.

RED BEFORE: at 7e170d62 every module below is REFUSED at the CLI gate
("--native-pointer-abi is memory-0-only in phase 1"), so the compile step of
this oracle fails. With the two refusals lifted and NO layering (the
RQ-88-MEMLAYER5 scratch lift), the same modules compile and MISCOMPILE: a
memory-1 static inside memory 0's window is rewritten to
`__synth_wasm_data + C` and then added to `__synth_wasm_data_1`. Measured on
that build: 34 of 43 calls diverge or leave their region, and all four
layering refusals compile instead.

HARNESS. Each object is hand-linked with every section at its own,
NON-ADJACENT base (`.text`, `.bss` = memory 0's reservation, `.data` =
memory 0's init segments + `__synth_globals`, `.synth.wasm_mem_1`, the host
stack) and the gaps between them UNMAPPED, so any stray access faults. Every
data access is hooked and classified by region; each export declares which
wasm memories it may touch and an access to any other memory's region is an
ISOLATION failure even when the result happens to be right. Caller-saved
registers beyond the arguments and the stack below SP are filled with
garbage. After every call the export's result AND both memories' full
contents are compared against wasmtime (memory 0 reconstructed from the
`.bss` reservation overlaid with the retargeted `.data` segments). Memory-0
pointer arguments are passed NATIVE (`__synth_wasm_data + p`, the ABI);
memory-k pointer arguments are wasm offsets.

FIXTURES (synthetic — gale's fused module is unpublished — each the shape
#1145 names):
  pages      memory 0 = 1 page, memory 1 = 2 pages, ONE `__stack_pointer` in
             memory 0, active data in BOTH memories, constant pointers into
             each memory (memory-1 statics INSIDE memory 0's window), a
             pointer routed through a local (#1568), through a call, through
             a block result, laundered through memory 1, a compare, a
             function using the shadow stack AND touching memory 1, and
             memory.size / memory.grow per memory.
  pagesize1  gale's measured combination (#1145, 2026-10-28): TWO DEFINED
             memories declared `(pagesize 1)` with byte extents of meld#530's
             order (memory 0 = 3000 B, memory 1 = 6000 B), data in both, the
             SP in memory 0 — plus the region-table pins: `__synth_mem_size_N`
             in BYTES, `__synth_mem_count`, `__synth_mem_base_1` at the base
             of `.synth.wasm_mem_1`.
  two_sp     one stack pointer PER domain, memory 1's init LARGER than memory
             0's but inside memory 0's extent — the single-memory pick takes
             memory 1's and rebases it into memory 0; the layered pick must not.
  two_sp_npa scripts/repro/memlayer5_1145/two_sp_npa.wat (RQ-88-MEMLAYER5's
             committed stand-in): memory 1's frame read through its own SP.
  launder01  a raw memory-1 constant stored in memory 0, loaded back and used
             as a memory-1 address (it must stay a wasm offset end to end).

THE OPT-IN ASSERTION `--embedder-copies-carry-no-pointers` (maintainer
decision, 2026-10-28). The pass is field-insensitive per memory, so a
cross-memory memory.copy joins the two memories' contents and a module that
stores pointers in BOTH memories is refused although no value is shared.
The flag lets the caller ASSERT the Canonical-ABI property — a cross-memory
copy never carries a value later used as an address in the DESTINATION
memory — and the pass then does not join contents at such a copy.
  xcopy_merge_flag    scripts/repro/npa_xcopy_merge_1145.wat (tenant keeps a
                      static pointer in its frame, supervisor follows a pointer
                      in memory 1, one memory.copy $m1 $m0): refused without
                      the flag (row xcopy_content_merge, whose message must
                      name the flag), executed bit-identical with it.
  xcopy_violate_flag  scripts/repro/npa_xcopy_violate_1145.wat VIOLATES the
                      assertion (the tenant's static pointer is copied into
                      memory 1 and dereferenced there): refused without the
                      flag (row xcopy_violate_noflag), and under the flag it
                      MUST diverge from wasmtime — the oracle fails if it does
                      not, because then the negative case would show nothing.
Memory 0 is compared POINTER-AWARE: an aligned word holding the native form
of a memory-0 offset where wasm holds the offset is the ABI, not a
divergence.

REFUSALS (each must refuse, naming the shape, no object written):
  both_mems      one constant used as an address in memory 0 AND memory 1;
  sp_both        the stack pointer used as an address in both memories;
  content_merge  a memory-0 static pointer stored in memory 0 in a module
                 where memory-0 contents also reach a memory-1 address — the
                 pass is field-insensitive per memory, so this refusal is
                 IMPRECISION, recorded as a still-refused shape;
  host_param     scripts/repro/mem406_multi_memory.wat: an EXPORT parameter
                 used as an address in both memories — the host cannot pass a
                 native pointer and a wasm offset at once;
  imported_mem0  an imported memory 0 beside a defined memory 1: the CLI sizes
                 memory 0's window from the DEFINED list, which is offset from
                 the memory index space, so the pass refuses rather than bound
                 the window by the wrong memory;
  xcopy_content_merge  the realistic shape that the cross-memory copy makes
                 refuse: a tenant storing a static pointer in its frame and
                 reading through it, a supervisor following a pointer stored in
                 memory 1, and ONE memory.copy $m1 $m0 between them. The copy
                 joins the two memories' contents in the field-insensitive
                 pass, so the tenant's constant reads as used in both memories.
                 Imprecision, measured: the same module without the adapter
                 compiles, and the plain (non-NPA) path compiles it;
  xcopy_nosp_static  a memory-0 static as the positional memory-0 side of a
                 cross-memory memory.copy in a module with NO stack-pointer
                 global: nothing relocates it, so the #1568 constant-address
                 guard refuses it (it compiled silently before the guard saw
                 the wrapped copy);
  safety_sw      `--safety-bounds software` (memory k has no size register).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/npa_multi_memory_1145_differential.py
Exits nonzero on any mismatch, isolation breach, missing refusal or vacuity.
"""

import os
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
                               UC_ARM_REG_R10, UC_ARM_REG_R11, UC_ARM_REG_R12,
                               UC_ARM_REG_SP)

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
R_ARM_ABS32 = 2
R_ARM_THM_CALL = 10
# Distinct, non-adjacent bases; everything between them is unmapped.
BASES = {".text": 0x0010_0000, ".bss": 0x0040_0000, ".data": 0x0080_0000,
         ".synth.wasm_mem_1": 0x0100_0000}
STACK_BASE, STACK_SIZE = 0x0200_0000, 0x1_0000
GARBAGE = 0xDEADBEEF

PAGES = r"""(module
  (memory $m0 1 1)
  (memory $m1 2 2)
  (global $sp (mut i32) (i32.const 0x1000))
  (data (memory $m0) (i32.const 0x2000) "\11\11\11\11\22\22\22\22\33\33\33\33")
  (data (memory $m1) (i32.const 0x2000) "\aa\aa\aa\aa\bb\bb\bb\bb\cc\cc\cc\cc")
  (data (memory $m1) (i32.const 0x10010) "\dd\dd\dd\dd")
  (func (export "read0_static") (result i32) (i32.load $m0 (i32.const 0x2004)))
  (func (export "read1_static") (result i32) (i32.load $m1 (i32.const 0x2004)))
  (func (export "read1_far") (result i32) (i32.load $m1 (i32.const 0x10010)))
  (func (export "read1_byte") (result i32) (i32.load8_u $m1 (i32.const 0x2009)))
  (func (export "read1_dyn") (param i32) (result i32) (i32.load $m1 (local.get 0)))
  (func (export "write0_dyn") (param i32 i32) (i32.store $m0 (local.get 0) (local.get 1)))
  (func (export "read0_dyn") (param i32) (result i32) (i32.load $m0 (local.get 0)))
  (func (export "read1_local") (result i32) (local i32)
    (local.set 0 (i32.const 0x2000)) (i32.load $m1 (local.get 0)))
  (func (export "read0_local") (result i32) (local i32)
    (local.set 0 (i32.const 0x2000)) (i32.load $m0 (local.get 0)))
  (func $h1 (param i32) (result i32) (i32.load $m1 (local.get 0)))
  (func $h0 (param i32) (result i32) (i32.load $m0 (local.get 0)))
  (func (export "via_call") (result i32)
    (i32.xor (call $h1 (i32.const 0x2004)) (call $h0 (i32.const 0x2008))))
  (func (export "write1_static") (param i32) (i32.store $m1 (i32.const 0x2008) (local.get 0)))
  (func (export "write0_static") (param i32) (i32.store $m0 (i32.const 0x2004) (local.get 0)))
  (func (export "launder1") (result i32)
    (i32.store $m1 (i32.const 0x3000) (i32.const 0x2004))
    (i32.load $m1 (i32.load $m1 (i32.const 0x3000))))
  (func (export "block1") (result i32)
    (i32.load $m1 (block (result i32) (i32.const 0x2000) (br 0))))
  (func (export "cmp1") (param i32) (result i32)
    (drop (i32.load $m1 (local.get 0)))
    (i32.lt_u (local.get 0) (i32.const 0x2004)))
  (func (export "both") (param i32) (result i32) (local $fp i32)
    (local.set $fp (i32.sub (global.get $sp) (i32.const 16)))
    (global.set $sp (local.get $fp))
    (i32.store $m0 offset=4 (local.get $fp) (local.get 0))
    (i32.store $m1 (i32.const 0x2000) (local.get 0))
    (local.set 0 (i32.add (i32.load $m0 offset=4 (local.get $fp))
                          (i32.load $m1 (i32.const 0x2004))))
    (global.set $sp (i32.add (local.get $fp) (i32.const 16)))
    (i32.add (local.get 0) (i32.load $m0 (i32.const 0x2000))))
  (func (export "size0") (result i32) (memory.size $m0))
  (func (export "size1") (result i32) (memory.size $m1))
  (func (export "grow1") (result i32) (memory.grow $m1 (i32.const 1)))
)"""
# (export, args, memories it may touch). An `n:` prefixed arg is a NATIVE
# memory-0 pointer: the harness passes `__synth_wasm_data + n`.
PAGES_CALLS = [
    ("read0_static", [], {0}), ("read1_static", [], {1}), ("read1_far", [], {1}),
    ("read1_byte", [], {1}), ("read1_dyn", [0x2000], {1}), ("read1_dyn", [0x10010], {1}),
    ("write0_dyn", ["n:0x1800", 0x12345678], {0}), ("read0_dyn", ["n:0x1800"], {0}),
    ("read1_local", [], {1}), ("read0_local", [], {0}), ("via_call", [], {0, 1}),
    ("write1_static", [0x0BADF00D], {1}), ("read1_dyn", [0x2008], {1}),
    ("write0_static", [0x600DCAFE], {0}), ("read0_static", [], {0}),
    ("launder1", [], {1}), ("block1", [], {1}), ("cmp1", [0x2000], {1}),
    ("cmp1", [0x2008], {1}), ("both", [0x01010101], {0, 1}),
    ("read1_static", [], {1}), ("size0", [], set()), ("size1", [], set()),
    ("grow1", [], set()), ("size1", [], set()),
]

PAGESIZE1 = r"""(module
  (memory $m0 3000 3000 (pagesize 1))
  (memory $m1 6000 6000 (pagesize 1))
  (global $sp (mut i32) (i32.const 0x400))
  (data (memory $m0) (i32.const 0x500) "\01\02\03\04\05\06\07\08")
  (data (memory $m1) (i32.const 0x500) "\a1\a2\a3\a4\a5\a6\a7\a8")
  (data (memory $m1) (i32.const 0x1500) "\f1\f2\f3\f4")
  (func (export "read0") (result i32) (i32.load $m0 (i32.const 0x504)))
  (func (export "read1") (result i32) (i32.load $m1 (i32.const 0x504)))
  (func (export "read1_far") (result i32) (i32.load $m1 (i32.const 0x1500)))
  (func (export "read1_local") (result i32) (local i32)
    (local.set 0 (i32.const 0x500)) (i32.load $m1 (local.get 0)))
  (func (export "write1") (param i32) (i32.store $m1 (i32.const 0x504) (local.get 0)))
  (func (export "write1_end") (param i32) (i32.store $m1 (i32.const 5996) (local.get 0)))
  (func (export "read1_end") (result i32) (i32.load $m1 (i32.const 5996)))
  (func (export "write0") (param i32) (i32.store $m0 (i32.const 0x500) (local.get 0)))
  (func (export "both") (param i32) (result i32) (local $fp i32)
    (local.set $fp (i32.sub (global.get $sp) (i32.const 32)))
    (global.set $sp (local.get $fp))
    (i32.store $m0 offset=8 (local.get $fp) (local.get 0))
    (i32.store $m1 (i32.const 0x600) (i32.load $m1 (i32.const 0x500)))
    (local.set 0 (i32.load $m0 offset=8 (local.get $fp)))
    (global.set $sp (i32.add (local.get $fp) (i32.const 32)))
    (i32.add (local.get 0) (i32.load $m1 (i32.const 0x600))))
  (func (export "size0") (result i32) (memory.size $m0))
  (func (export "size1") (result i32) (memory.size $m1))
)"""
PAGESIZE1_CALLS = [
    ("read0", [], {0}), ("read1", [], {1}), ("read1_far", [], {1}),
    ("read1_local", [], {1}), ("write1", [0x13579BDF], {1}), ("read1", [], {1}),
    ("write1_end", [0x2468ACE0], {1}), ("read1_end", [], {1}),
    ("write0", [0x55AA55AA], {0}), ("read0", [], {0}), ("both", [0x7F], {0, 1}),
    ("size0", [], set()), ("size1", [], set()),
]

TWO_SP = r"""(module
  (memory $m0 1 1)
  (memory $m1 1 1)
  (global $sp0 (mut i32) (i32.const 0x800))
  (global $sp1 (mut i32) (i32.const 0x4000))
  (data (memory $m0) (i32.const 0x1000) "\10\20\30\40")
  (data (memory $m1) (i32.const 0x1000) "\50\60\70\80")
  (func (export "frame0") (param i32) (result i32) (local $fp i32)
    (local.set $fp (i32.sub (global.get $sp0) (i32.const 16)))
    (i32.store $m0 (local.get $fp) (local.get 0))
    (i32.add (i32.load $m0 (local.get $fp)) (i32.load $m0 (i32.const 0x1000))))
  (func (export "frame1") (param i32) (result i32) (local $fp i32)
    (local.set $fp (i32.sub (global.get $sp1) (i32.const 16)))
    (global.set $sp1 (local.get $fp))
    (i32.store $m1 (local.get $fp) (local.get 0))
    (local.set 0 (i32.add (i32.load $m1 (local.get $fp)) (i32.load $m1 (i32.const 0x1000))))
    (global.set $sp1 (i32.add (local.get $fp) (i32.const 16)))
    (local.get 0))
  (func (export "sp1") (result i32) (global.get $sp1))
)"""
TWO_SP_CALLS = [
    ("frame0", [5], {0}), ("frame1", [7], {1}), ("sp1", [], set()),
]

LAUNDER01 = r"""(module
  (memory $m0 1 1)
  (memory $m1 1 1)
  (global $sp (mut i32) (i32.const 0x800))
  (data (memory $m1) (i32.const 0x2000) "\31\32\33\34")
  (func (export "launder01") (result i32)
    (i32.store $m0 (i32.const 0x900) (i32.const 0x2000))
    (i32.load $m1 (i32.load $m0 (i32.const 0x900))))
)"""
LAUNDER01_CALLS = [("launder01", [], {0, 1})]

HERE = Path(__file__).parent
# RQ-88-MEMLAYER5's committed stand-in for the `meld --domain` shape: one SP
# per domain, memory 1's init larger (refused at 7e170d62).
TWO_SP_FILE = (HERE / "memlayer5_1145" / "two_sp_npa.wat").read_text()
TWO_SP_FILE_CALLS = [("d1_frame_peek", [], {1})]

FIXTURES = [
    ("pages", PAGES, PAGES_CALLS),
    ("two_sp_npa", TWO_SP_FILE, TWO_SP_FILE_CALLS),
    ("pagesize1", PAGESIZE1, PAGESIZE1_CALLS),
    ("two_sp", TWO_SP, TWO_SP_CALLS),
    ("launder01", LAUNDER01, LAUNDER01_CALLS),
]

FLAG = "--embedder-copies-carry-no-pointers"
# The Rust-like adapter module: tenant keeps a static pointer in its frame
# and reads through it, supervisor follows a pointer stored in memory 1, one
# memory.copy $m1 $m0 between them. A Canonical-ABI copy: no copied value is
# used as an address in memory 1.
XCOPY_MERGE = (HERE / "npa_xcopy_merge_1145.wat").read_text()
XCOPY_MERGE_CALLS = [("tenant", [], {0}), ("sup", [], {1}),
                     ("adapter", [0x40, "n:0x1000", 4], {0, 1}), ("sup", [], {1}),
                     ("tenant", [], {0})]
# Violates the assertion: the tenant's static pointer is copied into memory 1
# and dereferenced THERE.
XCOPY_VIOLATE = (HERE / "npa_xcopy_violate_1145.wat").read_text()
XCOPY_VIOLATE_CALLS = [("tenant", [], {0}), ("adapter", [], {0, 1}), ("sup", [], {0, 1})]

REFUSE_NEEDLE = "no single representation"
REFUSALS = [
    ("both_mems", r"""(module (memory $m0 1 1) (memory $m1 1 1)
      (global $sp (mut i32) (i32.const 0x800))
      (data (memory $m0) (i32.const 0x1000) "\01")
      (func (export "f") (result i32) (local i32) (local.set 0 (i32.const 0x1000))
        (i32.add (i32.load $m0 (local.get 0)) (i32.load $m1 (local.get 0)))))""",
     [], "the constant 0x1000"),
    ("sp_both", r"""(module (memory $m0 1 1) (memory $m1 1 1)
      (global $sp (mut i32) (i32.const 0x800))
      (data (memory $m0) (i32.const 0x1000) "\01")
      (func (export "f") (result i32)
        (i32.add (i32.load $m0 (global.get $sp)) (i32.load $m1 (global.get $sp)))))""",
     [], "global 0"),
    ("content_merge", r"""(module (memory $m0 1 1) (memory $m1 1 1)
      (global $sp (mut i32) (i32.const 0x800))
      (data (memory $m0) (i32.const 0x1000) "\01\02\03\04")
      (func (export "copy") (i32.store $m1 (i32.const 0x10) (i32.load $m0 (i32.const 0x20))))
      (func (export "use1") (result i32) (i32.load $m1 (i32.load $m1 (i32.const 0x10))))
      (func (export "use0") (result i32)
        (i32.store $m0 (i32.const 0x20) (i32.const 0x1000))
        (i32.load $m0 (i32.load $m0 (i32.const 0x20)))))""",
     [], "the constant 0x1000"),
    ("host_param", (HERE / "mem406_multi_memory.wat").read_text(), [],
     "parameter 0 of exported function"),
    ("imported_mem0", r"""(module
      (import "env" "mem" (memory $m0 3000 3000 (pagesize 1)))
      (memory $m1 6000 6000 (pagesize 1))
      (global $sp (mut i32) (i32.const 0x400))
      (func (export "r1") (result i32) (i32.load $m1 (i32.const 0x500)))
      (func (export "r0") (result i32) (i32.load $m0 (i32.const 0x500))))""",
     [], "imports 1 of its memories"),
    ("xcopy_violate_noflag", (HERE / "npa_xcopy_violate_1145.wat").read_text(), [],
     "--embedder-copies-carry-no-pointers"),
    ("xcopy_content_merge", (HERE / "npa_xcopy_merge_1145.wat").read_text(), [],
     "--embedder-copies-carry-no-pointers"),
    ("xcopy_nosp_static", r"""(module (memory $m0 1 1) (memory $m1 1 1)
      (data (memory $m0) (i32.const 0x1000) "\11\22\33\44")
      (func (export "anchor") (result i32) (i32.load $m0 (i32.const 0x1000)))
      (func (export "x") (memory.copy $m1 $m0 (i32.const 0) (i32.const 0x1000) (i32.const 4))))""",
     [], "memory.copy (memory-0 side)"),
    ("safety_sw", PAGES, ["--safety-bounds", "software"], "memory 1"),
]


def compile_obj(wat, tmp, label, extra=()):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}.o"
    if obj.exists():
        obj.unlink()
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m3",
         "--all-exports", "--relocatable", "--native-pointer-abi", *extra],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    return r.returncode, (r.stdout or "") + (r.stderr or ""), obj


def wasmtime_instance(wat):
    cfg = wasmtime.Config()
    cfg.wasm_multi_memory = True
    cfg.wasm_custom_page_sizes = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, wat), [])
    return st, inst


def thm_bl(src, dst):
    off = dst - (src + 4)
    imm = (off >> 1) & 0xFFFFFF
    s, i1, i2 = (imm >> 23) & 1, (imm >> 22) & 1, (imm >> 21) & 1
    j1, j2 = (~(i1 ^ s)) & 1, (~(i2 ^ s)) & 1
    return struct.pack("<HH", 0xF000 | (s << 10) | ((imm >> 11) & 0x3FF),
                       0xD000 | (j1 << 13) | (j2 << 11) | (imm & 0x7FF))


def rup(n):
    return max(0x1000, (n + 0xFFF) & ~0xFFF)


class LayoutError(Exception):
    pass


class Linked:
    def __init__(self, obj):
        e = ELFFile(open(obj, "rb"))
        secs = list(e.iter_sections())
        self.sizes = {}
        self.blobs = {}
        self.aligns = {}
        for s in secs:
            if s.name in BASES:
                self.aligns[s.name] = s["sh_addralign"]
                self.sizes[s.name] = s["sh_size"]
                self.blobs[s.name] = b"" if s["sh_type"] == "SHT_NOBITS" else bytes(s.data())
        for need in (".text", ".synth.wasm_mem_1"):
            if need not in self.sizes:
                raise LayoutError(f"object has no {need} section")
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
                    self.syms[s.name] = (sec, s["st_value"], s["st_size"])
        text = bytearray(self.blobs[".text"])
        self.nrel = 0
        for r in e.get_section_by_name(".rel.text").iter_relocations():
            sym = symtab.get_symbol(r["r_info_sym"])
            if sym.name not in self.syms:
                sys.exit(f"unresolvable reloc target {sym.name!r}")
            dst = self.addr(sym.name)
            if r["r_info_type"] == R_ARM_ABS32:
                (add,) = struct.unpack_from("<I", text, r["r_offset"])
                struct.pack_into("<I", text, r["r_offset"], (dst + add) & 0xFFFFFFFF)
                self.nrel += 1
            elif r["r_info_type"] == R_ARM_THM_CALL:
                text[r["r_offset"]:r["r_offset"] + 4] = thm_bl(
                    BASES[".text"] + r["r_offset"], dst & ~1)
            else:
                sys.exit(f"unhandled reloc type {r['r_info_type']} for {sym.name}")
        self.text = bytes(text)
        if ".bss" not in self.sizes:
            # No memory-0 reservation was emitted: nothing relocates against
            # it, so memory 0 is host memory reached through native pointers.
            # Model it as a host region the size of memory 0.
            self.sizes[".bss"] = self.abs.get("__synth_mem_size_0", 0x1000)
            self.blobs[".bss"] = b""
            self.syms["__synth_wasm_data"] = (".bss", 0, 0)
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for name, base in BASES.items():
            self.mu.mem_map(base, rup(self.sizes.get(name, 0) + 0x20))
        self.mu.mem_map(STACK_BASE, STACK_SIZE)
        self.ret = BASES[".text"] + rup(len(self.text) + 0x20) - 0x10
        self.mu.mem_write(BASES[".text"], self.text)
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")
        for name in (".data", ".synth.wasm_mem_1"):
            if self.blobs.get(name):
                self.mu.mem_write(BASES[name], self.blobs[name])
        self.accesses = []
        self.mu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
                         lambda uc, acc, addr, size, val, ud: self.accesses.append((addr, size)))
        # Memory-0 segments: (wasm offset, length) -> packed `.data` address.
        self.segs = sorted(
            (int(n[len("__synth_wasm_seg_"):]), self.addr(n))
            for n in self.syms if n.startswith("__synth_wasm_seg_"))

    def addr(self, name):
        sec, val, _ = self.syms[name]
        return BASES[sec] + val

    def region(self, a):
        for name, base in BASES.items():
            if base <= a < base + max(self.sizes.get(name, 0), 1):
                if name == ".data":
                    g = self.syms.get("__synth_globals")
                    if g and a >= self.addr("__synth_globals"):
                        return "globals"
                    return "m0"
                return {".text": "text", ".bss": "m0", ".synth.wasm_mem_1": "m1"}[name]
        if STACK_BASE <= a < STACK_BASE + STACK_SIZE:
            return "stack"
        return f"OUTSIDE@{a:#x}"

    def native0(self, off):
        """The native address of memory-0 offset `off` under the ABI: inside
        a retargeted init segment (later-declared wins) or else the
        `__synth_wasm_data` reservation."""
        for k, a in reversed(self.segs):
            soff, ln = self.wasm_segs[k]
            if soff <= off < soff + ln:
                return a + (off - soff)
        return self.addr("__synth_wasm_data") + off

    def call(self, fn, args, mem0_size):
        sec, val, _ = self.syms[fn]
        base0 = self.addr("__synth_wasm_data")
        regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
        for i, r in enumerate(regs):
            self.mu.reg_write(r, GARBAGE ^ i)
        for i in range(8):  # r4..r11 hold garbage except the ABI registers
            self.mu.reg_write(UC_ARM_REG_R4 + i, GARBAGE ^ (0x100 * i))
        for i, a in enumerate(args):
            if isinstance(a, str):
                a = self.native0(int(a[2:], 16))
            self.mu.reg_write(regs[i], a & 0xFFFFFFFF)
        self.mu.reg_write(UC_ARM_REG_R12, GARBAGE)
        self.mu.reg_write(UC_ARM_REG_R11, 0)          # native deref (NPA)
        self.mu.reg_write(UC_ARM_REG_R10, mem0_size)  # memory 0 size in bytes
        sp = STACK_BASE + STACK_SIZE - 0x100
        self.mu.mem_write(STACK_BASE, bytes([0xA5]) * (STACK_SIZE - 0x100))
        self.mu.reg_write(UC_ARM_REG_SP, sp)
        self.mu.reg_write(UC_ARM_REG_LR, self.ret | 1)
        self.accesses = []
        try:
            self.mu.emu_start((BASES[sec] + val) | 1, self.ret, timeout=5_000_000)
        except UcError as ex:
            return f"FAULT {ex}", self.accesses
        return self.mu.reg_read(UC_ARM_REG_R0), self.accesses

    def mem0_image(self, wasm_segs, n):
        img = bytearray(self.mu.mem_read(BASES[".bss"], min(n, self.sizes[".bss"])))
        img += bytes(n - len(img))
        # Retargeted segments live in `.data`; later-declared wins.
        for (k, a) in self.segs:
            off, ln = wasm_segs[k]
            img[off:off + ln] = self.mu.mem_read(a, ln)
        return bytes(img)

    def mem1_image(self):
        return bytes(self.mu.mem_read(BASES[".synth.wasm_mem_1"], self.sizes[".synth.wasm_mem_1"]))


def mem0_segments(wat):
    """(offset, length) of memory 0's active segments, in declaration order."""
    import re
    out = []
    for m in re.finditer(r'\(data \(memory \$m0\) \(i32\.const (0x[0-9a-f]+)\) "([^"]*)"\)', wat):
        out.append((int(m.group(1), 16), m.group(2).count("\\")))
    return out


def mem0_equal(ln, mine, theirs, mem0_size):
    """Memory 0 under the native-pointer ABI holds a stored memory-0 POINTER
    in its native form (`__synth_wasm_data + C`, retargeted into its init
    segment), where wasm holds the offset C. An aligned word that differs
    only that way is the ABI, not a divergence; every other byte must be
    identical."""
    if mine == theirs:
        return True
    if len(mine) != len(theirs):
        return False
    for w in range(0, len(mine) - 3, 4):
        a, b = mine[w:w + 4], theirs[w:w + 4]
        if a == b:
            continue
        c = int.from_bytes(b, "little")
        if not (0 < c < mem0_size and int.from_bytes(a, "little") == ln.native0(c)):
            return False
    return mine[len(mine) - len(mine) % 4:] == theirs[len(theirs) - len(theirs) % 4:]


def run_fixture(label, wat, calls, tmp, extra=()):
    rc, log, obj = compile_obj(wat, tmp, label, extra)
    if rc != 0:
        print(f"[RED] {label}: compile rc={rc}: {log.strip().splitlines()[-1][:300]}")
        return 0, 1
    try:
        ln = Linked(obj)
    except LayoutError as ex:
        # e.g. memory 0's reservation never referenced: its statics were not
        # relocated at all — a failure of the object, not of the harness.
        print(f"[BUG] {label}: {ex}")
        return 0, 1
    if ln.nrel == 0:
        sys.exit(f"VACUOUS: {label} carries no ABS32 relocation")
    # Export both memories for comparison (the compiled module is unchanged).
    wat_x = wat.replace("(memory $m0 ", "(memory $m0 (export \"m0\") ", 1).replace(
        "(memory $m1 ", "(memory $m1 (export \"m1\") ", 1)
    st, inst = wasmtime_instance(wat_x)
    ex = inst.exports(st)
    w0, w1 = ex["m0"], ex["m1"]
    segs0 = mem0_segments(wat)
    ln.wasm_segs = segs0
    mem0_size = ln.abs.get("__synth_mem_size_0")
    if mem0_size is None:
        sys.exit(f"{label}: no __synth_mem_size_0")
    n_cmp = max([ln.sizes[".bss"]] + [o + n for o, n in segs0])
    fails = compared = 0
    for fn, args, allowed in calls:
        wargs = [int(a[2:], 16) if isinstance(a, str) else a for a in args]
        res = ex[fn](st, *wargs)
        got, accs = ln.call(fn, args, mem0_size)
        exp = None if res is None else res & 0xFFFFFFFF
        ok = isinstance(got, int) and (exp is None or got == exp)
        regions = {ln.region(a) for a, _ in accs}
        touched = {int(r[1]) for r in regions if r in ("m0", "m1")}
        stray = sorted(r for r in regions if r.startswith("OUTSIDE"))
        iso = not stray and touched <= allowed
        w0b = bytes(w0.read(st, 0, n_cmp))
        w1b = bytes(w1.read(st, 0, w1.data_len(st)))
        s0 = mem0_equal(ln, ln.mem0_image(segs0, n_cmp), w0b, mem0_size) and not any(
            bytes(w0.read(st, n_cmp, w0.data_len(st))))
        s1 = ln.mem1_image()[:len(w1b)] == w1b
        good = ok and iso and s0 and s1
        compared += 1
        fails += not good
        shown = got if isinstance(got, str) else hex(got)
        note = "" if good else (
            f"  <-- {'' if ok else 'RESULT '}{'' if iso else f'ISOLATION touched={sorted(touched)} allowed={sorted(allowed)} {stray} '}"
            f"{'' if s0 else 'MEM0 '}{'' if s1 else 'MEM1'}")
        print(f"  [{'ok ' if good else 'BUG'}] {label}.{fn}{tuple(args)} -> {shown} "
              f"(wasmtime {exp if exp is None else hex(exp)}) mems={sorted(touched)}{note}")
    return compared, fails


def check_region_table(tmp):
    """gale's combination: `(pagesize 1)` byte extents in the region table."""
    rc, log, obj = compile_obj(PAGESIZE1, tmp, "pagesize1_table")
    if rc != 0:
        print(f"[RED] region table: compile rc={rc}")
        return 1
    try:
        ln = Linked(obj)
    except LayoutError as ex:
        print(f"[BUG] region table: {ex}")
        return 1
    # `__synth_mem_region_N` is the PMSAv7-legal extent the embedder programs
    # the MPU from: `mpu_region_align` in crates/synth-cli/src/main.rs —
    # next power of two of the BYTE size, at least 32: 3000 -> 4096,
    # 6000 -> 8192. Memory 1's section is aligned to its region.
    def pmsa(n):
        return max(32, 1 << (n - 1).bit_length())
    want = {"__synth_mem_count": 2, "__synth_mem_size_0": 3000, "__synth_mem_size_1": 6000,
            "__synth_mem_region_0": pmsa(3000), "__synth_mem_region_1": pmsa(6000)}
    bad = 0
    for k, v in want.items():
        got = ln.abs.get(k)
        print(f"  [{'ok ' if got == v else 'BUG'}] {k} = {got} (want {v})")
        bad += got != v
    sec, val, size = ln.syms.get("__synth_mem_base_1", (None, None, None))
    ok = sec == ".synth.wasm_mem_1" and val == 0 and ln.sizes[sec] >= 6000
    print(f"  [{'ok ' if ok else 'BUG'}] __synth_mem_base_1 at {sec}+{val} "
          f"(section {ln.sizes.get('.synth.wasm_mem_1')} B >= 6000)")
    bad += not ok
    al = ln.aligns.get(".synth.wasm_mem_1")
    print(f"  [{'ok ' if al == pmsa(6000) else 'BUG'}] .synth.wasm_mem_1 sh_addralign = {al} "
          f"(want {pmsa(6000)}, its MPU region)")
    bad += al != pmsa(6000)
    if "__synth_mem_base_0" in ln.syms:
        print("  [BUG] __synth_mem_base_0 present (memory 0 has no link-time base)")
        bad += 1
    return bad


def main():
    tmp = Path(tempfile.mkdtemp(prefix="npa_mm_1145_"))
    total = fails = 0
    for label, wat, calls in FIXTURES:
        print(f"=== {label} ===")
        c, f = run_fixture(label, wat, calls, tmp)
        total += c
        fails += f
    # --embedder-copies-carry-no-pointers (maintainer decision, 2026-10-28):
    # the caller ASSERTS that a cross-memory memory.copy carries no value
    # later used as an address in the destination memory, so the pass does
    # not join the two memories' contents there.
    print(f"=== {FLAG}: the Rust-like adapter module (refused without it) ===")
    c, f = run_fixture("xcopy_merge_flag", XCOPY_MERGE, XCOPY_MERGE_CALLS, tmp, [FLAG])
    total += c
    fails += f
    # The NEGATIVE half: the assertion is FALSE for this module (it copies a
    # pointer across memories and dereferences it in the destination), so
    # under the flag it must NOT match wasmtime — that divergence is the
    # obligation the flag hands the caller. Without the flag it is refused.
    print(f"=== {FLAG} with the obligation VIOLATED: must diverge ===")
    c, f = run_fixture("xcopy_violate_flag", XCOPY_VIOLATE, XCOPY_VIOLATE_CALLS, tmp, [FLAG])
    total += c
    if f == 0:
        print("  [BUG] the violated assertion produced no divergence — the negative "
              "case is not showing what the flag's obligation guards")
        fails += 1
    else:
        print(f"  [ok ] {f} call(s) diverge from wasmtime, as a false assertion must")
    print("=== region table (pagesize 1, bytes) ===")
    fails += check_region_table(tmp)
    print("=== refusals ===")
    refused = 0
    for label, wat, extra, needle in REFUSALS:
        rc, log, obj = compile_obj(wat, tmp, f"refuse_{label}", extra)
        ok = (rc != 0 and "panicked" not in log and needle in log
              and (label in ("safety_sw", "imported_mem0", "xcopy_nosp_static")
                   or REFUSE_NEEDLE in log)
              and not (obj.exists() and obj.stat().st_size > 0))
        print(f"  [{'ok ' if ok else 'BUG'}] refused: {label} (rc={rc})"
              + ("" if ok else f"\n{log[-600:]}"))
        refused += ok
    if refused != len(REFUSALS):
        fails += len(REFUSALS) - refused
    if total < 40:
        print(f"VACUOUS: compared {total} calls")
        return 1
    print(f"\ncompared: {total}")
    print(f"refusals: {refused}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
