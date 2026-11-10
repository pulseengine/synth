#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 62
"""RQ-91-NPAMODEL (#1672, #1568, #1604, #1661): memory-0 address provenance
under `--relocatable --native-pointer-abi` is decided ONCE per module, and
every shape is either executed equal to wasmtime or refused loudly with a
named diagnostic — execution differential, red on eab66646, green after.

Under the ABI R11 is 0: a memory-0 access dereferences its address as a
NATIVE pointer, and a wasm static at `C` lives at `__synth_wasm_data + C`.
The module-level decision (`Provenance::memory0_plan`) names the constants to
relocate or refuses the module; the ARM backend validates the emitted stream
(`npa-addr-validate`). Rows, one per shape (EXEC = executed against wasmtime
on the hand linker of npa_const_addr_differential.py, one instance per row):

  #1672 data pointer
    datap_neg     a data word holding a wasm address, loaded and dereferenced
                  (the issue's repro): REFUSED `npa-data-pointer (#1672)`,
                  naming the function, the load site and the segment offset.
                  On eab66646 it compiled and faulted on the raw address.
    str_neg       the `&'static str` shape: segment 1 holds a pointer to a
                  string in segment 0, loaded and dereferenced byte-wise:
                  REFUSED with the same diagnostic.
    datap_near    NEAR MISS: the same pointer word loaded and RETURNED (never
                  dereferenced): EXEC.
    bump_pos      gale's bump allocator (POSITIVE CONTROL): `static mut HEAP`
                  and `static mut OFF` with a stack-pointer global;
                  `alloc(n)` returns HEAP + OFF and bumps OFF — a load from a
                  static flowing into an address as an INDEX on a static
                  base. A store through the returned pointer and a load back:
                  EXEC.
  #1568 residuals
    arith / sel   a constant static through arithmetic and through a select:
                  EXEC (eab66646 faulted on both, 1 of 4 equal).
    local_arith   a constant through a local whose definition is arithmetic:
                  EXEC.
    mmio_pos      no data segment, no stack-pointer global: `0x40000000 +` a
                  run-time offset is NATIVE (R2, the MMIO_BASE + reg shape):
                  compiles; executed on the native contract (unicorn maps the
                  peripheral page; wasmtime cannot address it).
  #1604 residuals
    straddle_neg  `i32.const 0xffe + 0` straddling the reservation into a
                  segment: REFUSED `npa-region-straddle (#1604)`.
    fill_neg      `memory.fill` with a COMPUTED constant destination and a
                  run-time length: REFUSED `npa-region-straddle (#1604)`.
    inregion      near miss: `0x1000 + 2` inside the segment: EXEC.
  shape 6 (stack-pointer init ABOVE data)
    below_sp      SP at 0x2000, data at 0x1000 and 0x3000: the positional and
                  the arithmetic constant below the SP and the static above
                  it: EXEC (eab66646 faulted on the two below it).
    below_sp_dyn  a run-time base plus an offset into the data below the SP:
                  REFUSED `npa-dynamic-static-offset (#1568)`.
  R1 boundary (one past a segment's end)
    gale_boundary gale's shape: adjacent segments [2048, 2056) and [2056,
                  2057), a flag at 2056 read and written: EXEC.
    end_cmp_neg   `while p != END` with END one past segment 0: REFUSED
                  `npa-end-pointer-compare (#1604)` (eab66646: 0x1043, wasmtime 0x3).
    end_ltu_neg / end_i64_neg / end_i64c_neg
                  the same walk as `p < END`, as an i64 comparison of the
                  extended END, and against an `i64.const` END: REFUSED, same
                  diagnostic (eab66646: 0x1043, 0x1043, a fault).
    end_scalar_neg
                  a counter compared with a constant equal to a segment end:
                  REFUSED (eab66646 relocated the constant and never stopped).
    interior_cmp  the walk compared against 0x2008 inside one segment: EXEC.
  #1684 i64 constants (never relocated)
    i64_static_cmp_neg / i64_static_addr_neg
                  an i64.const in the static window compared with a
                  static-derived pointer (eab66646 faulted, wasmtime 0x3), or
                  reaching a memory-0 address: REFUSED `npa-i64-static-const
                  (#1684)`.
    i64_outside_ctl / i64_scalar_ctl / i64_hostcmp_ctl / i64_counter_ctl
                  an i64.const outside the window, a plain scalar, compared
                  with a host value, an i64 counter bound: EXEC.
  gale's census of 257f0067 (three false-positive classes)
    gale_fp2a     a dead core::fmt pad_integral dereferencing a panic
                  Location pointer: EXEC (257f0067 refused it).
    gale_fp2b     a state machine's next-state load beside a stored Location
                  pointer: EXEC (257f0067 refused it).
    gale_fp2a_direct_neg / gale_fp2a_indirect_neg
                  the same dereference reachable directly / only through
                  call_indirect: REFUSED `npa-data-pointer (#1672)`.
    ptrtab_idx_neg
                  a pointer table read through a scaled index and
                  dereferenced: REFUSED (eab66646 and 257f0067 compiled it
                  and faulted where wasmtime returns 97).
    (the memory-1 shift-count false positive is gale_fp1 in
    npa_multi_memory_1145_differential.py)
  gale's census of 85e5f200
    gale_fpA      a live dereference whose only data-word source is a dead
                  function's load: EXEC (85e5f200 refused it).
    gale_fpB      one method called on two statics in two segments: EXEC
                  (85e5f200 refused it as npa-region-straddle).
    gale_fpA_indirect_neg / gale_fpB_neg
                  the source reachable through call_indirect / one instance
                  straddling its segment end: REFUSED.
  gale's census of c9288222
    gale_fpA1     a static's address through two call levels, loaded and
                  dereferenced, while another caller passes &Location
                  through the same chain: EXEC (c9288222 refused it).
    gale_fpA2     a cabi_realloc_* grow copy from old_ptr: EXEC (c9288222
                  refused it).
    gale_fpA1_ctx_neg / gale_fpA1_straddle_neg / gale_fpA2_*_neg
                  the Location caller's own dereference, a true straddle,
                  the realloc shape under another name or signature, a copy
                  from a pointer-bearing constant, a copy from a non-realloc
                  export's param (R3'): REFUSED.
  gale's real modules at 3775050e (sha256s in RQ-91-NPAMODEL)
    gale_gfA1 / gale_gfA1_fill / gale_gfA2
                  minimal reproductions of the fused v11 one-domain image's
                  two refusals and gustos.loom's: EXEC (3775050e refused
                  each with gale's diagnostic text).
    gale_gf_ptrtab_site_neg / gale_gf_field_neg / gale_gfA2_mixed_neg
                  REFUSED.
  #1661
    swb_neg       `--safety-bounds software` on a module touching memory 0:
                  REFUSED `npa-software-bounds (#1661)` (eab66646 compiled
                  and trapped every in-bounds access).

Run: SYNTH=./target/debug/synth python3 scripts/repro/npa_model_differential.py
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import wasmtime  # noqa: E402
import npa_const_addr_differential as h  # noqa: E402

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

SEG = '(module (memory (export "mem") 1)\n  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88")\n'
ANCHOR = '  (func (export "anchor") (result i32) (i32.load (i32.const 0x1000)))\n'
# R1 boundary rows: `p = 0x2000; loop { if EXIT break; s += *p; p += 4 }`
# with a stack pointer at 0x1000, so every segment is on the split layout.
WALK_SP = '(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x1000))\n'
WALK_SEG2 = ('  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00")\n'
             '  (data (i32.const 0x3000) "\\40\\00\\00\\00")\n')


def walk(exit_cond):
    return ('  (func (export "sum") (result i32) (local i32 i32)\n'
            '    (local.set 0 (i32.const 0x2000))\n'
            '    (block (loop\n'
            f'      (br_if 1 {exit_cond})\n'
            '      (local.set 1 (i32.add (local.get 1) (i32.load (local.get 0))))\n'
            '      (local.set 0 (i32.add (local.get 0) (i32.const 4)))\n'
            '      (br 0)))\n'
            '    (local.get 1)))')



EXEC = [
    ("datap_near",
     '(module (memory 5376 (pagesize 1))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88\\04\\10\\00\\00")\n'
     + ANCHOR +
     '  (func (export "word") (result i32) (i32.load (i32.const 0x1008))))',
     [("anchor", ()), ("word", ())]),
    ("bump_pos",
     '(module (memory (export "mem") 2)\n'
     '  (global $sp (mut i32) (i32.const 0x10000))\n'
     '  (data (i32.const 0x10000) "\\de\\c0\\ad\\0b")\n'
     # HEAP: 0x10100..0x10200 (BSS), OFF: 0x10010 (BSS word)
     '  (func $alloc (export "alloc") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (i32.add (i32.const 0x10100) (i32.load (i32.const 0x10010))))\n'
     '    (i32.store (i32.const 0x10010) (i32.add (i32.load (i32.const 0x10010)) (local.get 0)))\n'
     '    (local.get 1))\n'
     '  (func (export "use") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (call $alloc (i32.const 8)))\n'
     '    (i32.store (local.get 1) (local.get 0))\n'
     '    (i32.store offset=4 (local.get 1) (i32.const 0x5a5a5a5a))\n'
     '    (i32.add (i32.load (local.get 1)) (i32.load offset=4 (local.get 1))))\n'
     '  (func (export "off") (result i32) (i32.load (i32.const 0x10010)))\n'
     '  (func (export "heap0") (result i32) (i32.load (i32.const 0x10100)))\n'
     '  (func (export "heap8") (result i32) (i32.load (i32.const 0x10108)))\n'
     '  (func (export "anchor") (result i32) (i32.load (i32.const 0x10000))))',
     [("use", (0x11111111,)), ("off", ()), ("heap0", ()), ("use", (0x22222222,)),
      ("off", ()), ("heap8", ()), ("anchor", ())]),
    # The same allocator in an image whose data DOES hold a wasm address
    # (a vtable-like word at 0x10000 naming 0x10004) that is never
    # dereferenced: it must not make the allocator refuse.
    ("bump_ptrdata",
     '(module (memory (export "mem") 2)\n'
     '  (global $sp (mut i32) (i32.const 0x10000))\n'
     '  (data (i32.const 0x10000) "\\04\\00\\01\\00\\de\\c0\\ad\\0b")\n'
     '  (func $alloc (export "alloc") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (i32.add (i32.const 0x10100) (i32.load (i32.const 0x10010))))\n'
     '    (i32.store (i32.const 0x10010) (i32.add (i32.load (i32.const 0x10010)) (local.get 0)))\n'
     '    (local.get 1))\n'
     '  (func (export "use") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (call $alloc (i32.const 8)))\n'
     '    (i32.store (local.get 1) (local.get 0))\n'
     '    (i32.load (local.get 1)))\n'
     '  (func (export "vt") (result i32) (i32.load (i32.const 0x10000))))',
     [("use", (0x33333333,)), ("use", (0x44444444,)), ("vt", ())]),
    # gale's R1 boundary shape: two ADJACENT segments [2048, 2056) and
    # [2056, 2057), a run-once flag at 2056 read and written through
    # `offset=2056` (positional and run-time base). The constant one past
    # the first segment resolves to the START of the region holding it — the
    # second segment — which is what these accesses mean.
    ("gale_boundary",
     '(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 1024))\n'
     '  (data (i32.const 2048) "\\01\\02\\03\\04\\05\\06\\07\\08")\n'
     '  (data (i32.const 2056) "\\00")\n'
     '  (func (export "flag") (result i32) (i32.load8_u offset=2056 (i32.const 0)))\n'
     '  (func (export "set") (i32.store8 offset=2056 (i32.const 0) (i32.const 1)))\n'
     '  (func (export "flag_rt") (param i32) (result i32) (i32.load8_u offset=2056 (local.get 0)))\n'
     '  (func (export "set_rt") (param i32) (i32.store8 offset=2056 (local.get 0) (i32.const 7)))\n'
     '  (func (export "w6") (result i32) (i32.load (i32.const 2052))))',
     [("flag", ()), ("set", ()), ("flag", ()), ("w6", ()), ("set_rt", (0,)),
      ("flag_rt", (0,)), ("flag", ())]),
    ("arith_sel", SEG + ANCHOR +
     '  (func (export "arith") (result i32) (i32.load (i32.add (i32.const 0x1000) (i32.const 4))))\n'
     '  (func (export "sel") (param i32) (result i32)\n'
     '    (i32.load (select (i32.const 0x1000) (i32.const 0x1004) (local.get 0))))\n'
     '  (func (export "local_arith") (result i32) (local i32)\n'
     '    (local.set 0 (i32.sub (i32.const 0x1006) (i32.const 2)))\n'
     '    (i32.load (local.get 0))))',
     [("anchor", ()), ("arith", ()), ("sel", (1,)), ("sel", (0,)), ("local_arith", ())]),
    ("inregion", SEG + ANCHOR +
     '  (func (export "f") (result i32) (i32.load (i32.add (i32.const 0x1000) (i32.const 2)))))',
     [("anchor", ()), ("f", ())]),
    ("below_sp",
     '(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x2000))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88")\n'
     '  (data (i32.const 0x3000) "\\aa\\bb\\cc\\dd")\n'
     '  (func (export "hi") (result i32) (i32.load (i32.const 0x3000)))\n'
     '  (func (export "lo") (result i32) (i32.load (i32.const 0x1000)))\n'
     '  (func (export "lo4") (result i32) (i32.load (i32.const 0x1004)))\n'
     '  (func (export "lo_arith") (result i32) (i32.load (i32.add (i32.const 0x1000) (i32.const 4)))))',
     [("hi", ()), ("lo", ()), ("lo4", ()), ("lo_arith", ())]),
    # R1 boundary near miss: the same walk compared against 0x2008 INSIDE one
    # segment [0x2000, 0x2010) — not a boundary, so not refused: EXEC.
    ("interior_cmp", WALK_SP +
     '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00\\04\\00\\00\\00\\08\\00\\00\\00")\n'
     + walk('(i32.eq (local.get 0) (i32.const 0x2008))'),
     [("sum", ())]),
    # #1684 controls: an i64.const that is NOT refused. Outside the static
    # window; inside it but a plain scalar; inside it but compared with a host
    # value; an i64 counter compared with an in-window bound. Each EXEC, and
    # byte-identical to eab66646.
    ("i64_outside_ctl", WALK_SP + '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00\\04\\00\\00\\00\\08\\00\\00\\00")\n' + '  (func (export "anchor") (result i32) (i32.load (i32.const 0x2004)))\n' +
     '  (func (export "c") (result i32) (i64.eq (i64.extend_i32_u (i32.const 0x2000)) (i64.const 0x10))))',
     [("anchor", ()), ("c", ())]),
    ("i64_scalar_ctl", WALK_SP + '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00\\04\\00\\00\\00\\08\\00\\00\\00")\n' + '  (func (export "anchor") (result i32) (i32.load (i32.const 0x2004)))\n' +
     '  (func (export "s") (result i32) (i32.wrap_i64 (i64.add (i64.const 0x2004) (i64.const 1)))))',
     [("anchor", ()), ("s", ())]),
    ("i64_hostcmp_ctl", WALK_SP + '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00\\04\\00\\00\\00\\08\\00\\00\\00")\n' + '  (func (export "anchor") (result i32) (i32.load (i32.const 0x2004)))\n' +
     '  (func (export "h") (param i32) (result i32) (i64.eq (i64.extend_i32_u (local.get 0)) (i64.const 0x2004))))',
     [("anchor", ()), ("h", (0x2004,)), ("h", (5,))]),
    # gale's false positives on 257f0067 (census of its real images), each
    # REFUSED there and EXEC here. fp2a: a core::fmt pad_integral that
    # dereferences a panic Location's file pointer, reachable only through
    # the element table whose only call_indirect is inside the same dead
    # cluster (npa-data-pointer applies to reachable functions only). fp2b:
    # a state machine whose next-state load sat in the same bucket as a
    # stored Location pointer, because every `offset=N (i32.const 0)` access
    # shared one (offset-aware buckets: a run-time index beside a static
    # memarg base stays in the base's region).
    ("gale_fp2a", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (type $t (func (param i32) (result i32)))
  (table 2 funcref) (elem (i32.const 0) $fmt $pad)
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func $pad (param i32) (result i32) (i32.load8_u (i32.load (i32.const 0x84c))))
  (func $fmt (param i32) (result i32) (call_indirect (type $t) (local.get 0) (i32.const 1)))
  (func (export "anchor") (result i32) (i32.load8_u (i32.const 0x840)))
  )""", [("anchor", ())]),
    ("gale_fp2b", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x938) "\04\00\00\00\08\00\00\00\0c\00\00\00\00\00\00\00\0a\00\00\00\14\00\00\00\1e\00\00\00\28\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func (export "loc") (result i32) (i32.store offset=0x900 (i32.const 0) (i32.const 0x84c)) (i32.const 0))
  (func (export "f5") (result i32) (local i32)
    (local.set 0 (i32.load offset=2412 (i32.const 0)))
    (if (i32.ge_u (local.get 0) (i32.const 16)) (then (return (i32.const 0))))
    (i32.load offset=2376 (local.get 0)))
  (func (export "f9") (param i32) (local i32)
    (local.set 1 (select (i32.load offset=2412 (i32.const 0)) (i32.const 4) (local.get 0)))
    (i32.store offset=2412 (i32.const 0) (i32.load offset=2360 (local.get 1)))))""",
     [("loc", ()), ("f5", ()), ("f9", (0,)), ("f5", ()), ("f9", (1,)), ("f5", ()), ("f9", (0,)), ("f5", ())]),
    # gale's census of 85e5f200: fpA, a reachable function dereferencing a
    # pointer it stored to its own stack slot, where the "data word" came
    # only from a DEAD pad_integral storing a Location word to the same
    # slot (a source load must be reachable too); fpB, one method called on
    # two statics in two segments, `check(0x938)` and `check(0x978)`, each
    # struct inside its own segment (the bases are judged per element, not
    # as a union). Both refused on 85e5f200, EXEC here.
    ("gale_fpA", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (type $t (func (param i32) (result i32)))
  (table 1 funcref) (elem (i32.const 0) $pad)
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x900) "\2a\00\00\00")
  (func $pad (param i32) (result i32)
    (i32.store (i32.sub (global.get $sp) (i32.const 16)) (i32.load (i32.const 0x84c)))
    (i32.const 0))
  (func (export "state") (result i32)
    (i32.store (i32.sub (global.get $sp) (i32.const 16)) (i32.const 0x900))
    (i32.load (i32.load (i32.sub (global.get $sp) (i32.const 16)))))
  )""", [("state", ())]),
    ("gale_fpB", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x938) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\01\01\00\00\02\01\00\00\03\01\00\00\04\01\00\00\05\01\00\00\06\01\00\00\07\01\00\00\08\01\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x974) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\01\02\00\00\02\02\00\00\03\02\00\00\04\02\00\00\05\02\00\00\06\02\00\00\07\02\00\00\08\02\00\00\00")
  (func $check (param i32) (result i32)
    (i32.add (i32.load offset=16 (local.get 0))
      (i32.add (i32.load offset=32 (local.get 0)) (i32.load offset=48 (local.get 0)))))
  (func (export "a") (result i32) (call $check (i32.const 0x938)))
  (func (export "b") (result i32) (call $check (i32.const 0x978))))""", [("a", ()), ("b", ())]),
    # gale's census of c9288222. fpA1: a static at the start of the segment
    # after the Location's, its address passed through two call levels and
    # loaded; another caller passes `&Location` through the same chain, and
    # the context-insensitive return made EVERY call's result "maybe the
    # Location word" (the refusal now needs a call/return-matched path), and
    # its `+128` sibling is judged per base. fpA2: a wit-bindgen-shaped
    # `cabi_realloc_*` whose grow copy reads `old_ptr` (param 0): under the
    # canonical-ABI realloc contract that is a prior allocation, not a
    # static. Both refused on c9288222, EXEC here.
    ("gale_fpA1", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x1020) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\30\10\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x1188) "\00\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func $f60 (param i32 i32 i32) (result i32)
    (i32.add (i32.load (local.get 1)) (i32.mul (local.get 2) (i32.load (i32.add (local.get 1) (i32.const 128))))))
  (func $f61 (param i32 i32) (result i32)
    (call $f60 (i32.add (global.get $sp) (i32.const 8)) (local.get 0) (local.get 1)))
  (func (export "loc") (result i32) (call $f61 (i32.const 0x109c) (i32.const 0)))
  (func (export "run") (result i32)
    (i32.store (i32.const 0x1188) (i32.const 0x1030))
    (i32.load8_u (call $f61 (i32.const 4488) (i32.const 0)))))""", [("run", ())]),
    ("gale_fpA2", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x880) "hello\00\00\00")
  (func $impl (export "cabi_realloc_wit_bindgen_0_52_0") (param i32 i32 i32 i32) (result i32) (local i32)
    (local.set 4 (i32.add (i32.const 0xa00) (i32.load (i32.const 0x900))))
    (i32.store (i32.const 0x900) (i32.add (i32.load (i32.const 0x900)) (i32.const 16)))
    (if (local.get 0)
      (then (memory.copy (local.get 4) (local.get 0)
              (select (local.get 1) (local.get 3) (i32.lt_u (local.get 1) (local.get 3))))))
    (local.get 4))
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) (call $impl (local.get 0) (local.get 1) (local.get 2) (local.get 3)))
  (func (export "loc") (result i32) (i32.const 0x84c))
  (func (export "run") (result i32) (local i32 i32)
    (local.set 0 (call $impl (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 0) (i32.const 0x880))
    (local.set 1 (call $impl (local.get 0) (i32.const 4) (i32.const 4) (i32.const 8)))
    (i32.load8_u (i32.load (local.get 1)))))""", [("run", ())]),
    # gale's REAL modules (3775050e, base 0185ba07): minimal reproductions,
    # each refused on 3775050e with gale's diagnostic text, EXEC here.
    # gfA1: fused v11 one-domain. The source load reads `4488 + 192 +
    # (host << 5)` and the host value carries the Location segment's
    # escaped region (R1 now judges a static base plus a run-time delta by
    # the base's segment); the loaded word reaches a reused local that is
    # the index of `i32.load offset=7336` (a static memarg base anchors,
    # like HEAP + OFF). gfA1_fill: the same image's next refusal, a local
    # reused as a memory.fill destination (7384) and a memory.copy
    # destination (7320), plus its implicit zero (the per-base rule compares
    # in-window values only). gfA2: gustos.loom's wit-bindgen realloc reads
    # old_ptr through rustc's spill `local.set 6` (R4 follows unchanged
    # copies).
    ("gale_gfA1", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 4128) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\5f\10\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 4488) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 7320) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\0b\00\00\00\16\00\00\00\21\00\00\00\2c\00\00\00\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func $f60 (param i32 i32 i32)
    (local.set 1 (i32.add (i32.add (i32.shl (local.get 2) (i32.const 5)) (local.get 1)) (i32.const 192)))
    (i32.store offset=7372 (i32.const 0) (i32.load (local.get 1))))
  (func $f61 (param i32 i32) (call $f60 (i32.add (global.get $sp) (i32.const 8)) (local.get 0) (local.get 1)))
  (func $f45 (param i32) (call $f61 (i32.const 4488) (local.get 0)))
  (func $f6 (param i32) (result i32) (local i32 i32)
    (local.set 2 (i32.const 0))
    (block (local.set 2 (local.tee 2 (i32.load offset=7372 (i32.const 0))))
      (br_if 0 (i32.lt_u (local.get 2) (i32.const 4)))
      (return (i32.const 0)))
    (i32.add (i32.load offset=7336 (local.tee 2 (i32.shl (local.get 2) (i32.const 2))))
             (i32.load offset=7352 (local.get 2))))
  (func (export "gust:mpu/iso@0.1.0#switch-to-partition") (param i32) (result i32)
    (call $f45 (i32.and (local.get 0) (i32.const 3)))
    (call $f6 (local.get 0)))
  (func (export "loc") (result i32) (i32.const 0x109c)))""",
     [("gust:mpu/iso@0.1.0#switch-to-partition", (0,)), ("gust:mpu/iso@0.1.0#switch-to-partition", (1,)),
      ("gust:mpu/iso@0.1.0#switch-to-partition", (2,)), ("gust:mpu/iso@0.1.0#switch-to-partition", (3,))]),
    ("gale_gfA1_fill", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 7320) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\55\00\00\00")
  (data (i32.const 7380) "\00\00\00\00\00\01\00\00\01\01\00\00\02\01\00\00\03\01\00\00\04\01\00\00\05\01\00\00\06\01\00\00\07\01\00\00\08\01\00\00\09\01\00\00\0a\01\00\00\0b\01\00\00\0c\01\00\00\00")
  (func $f6 (param i32) (result i32) (local i32 i32 i32 i32)
    (block
      (br_if 0 (i32.load offset=7380 (i32.const 0)))
      (i32.store offset=7380 (i32.const 0) (i32.const 1))
      i32.const 7384
      i32.const 0
      i32.const 52
      local.set 3
      local.set 4
      local.set 1
      local.get 1
      local.get 4
      local.get 3
      memory.fill)
    i32.const 7320
    i32.const 7384
    i32.const 52
    local.set 3
    local.set 2
    local.set 1
    local.get 1
    local.get 2
    local.get 3
    memory.copy
    (i32.add (i32.load offset=7336 (i32.const 0)) (i32.load offset=7376 (i32.const 0))))
  (func (export "run") (result i32) (call $f6 (i32.const 0))))""", [("run", ())]),
    ("gale_gfA2", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\43\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x8a0) "\68\65\6c\6c\6f\00\00\00\00\00\00\00\00\00\00\00")
  (func $realloc (export "cabi_realloc_wit_bindgen_0_52_0") (param i32 i32 i32 i32) (result i32) (local i32 i32 i32 i32 i32)
    (local.set 2 (i32.add (i32.const 2524) (i32.load offset=3548 (i32.const 0))))
    (i32.store offset=3548 (i32.const 0) (i32.add (i32.load offset=3548 (i32.const 0)) (i32.const 16)))
    (local.set 3 (select (local.get 3) (local.get 1) (i32.lt_u (local.get 3) (local.get 1))))
    (if (local.get 0) (then
      local.get 2
      local.get 0
      local.get 3
      local.set 7
      local.set 6
      local.set 5
      local.get 5
      local.get 6
      local.get 7
      memory.copy))
    (local.get 2))
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
    (call $realloc (local.get 0) (local.get 1) (local.get 2) (local.get 3)))
  (func (export "loc") (result i32) (i32.const 0x86c))
  (func (export "gust:sched/tasks@0.1.0#state") (result i32) (local i32 i32)
    (local.set 0 (call $realloc (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 0) (i32.const 0x8a0))
    (local.set 1 (call $realloc (local.get 0) (i32.const 4) (i32.const 4) (i32.const 8)))
    (i32.load8_u (i32.load (local.get 1)))))""", [("gust:sched/tasks@0.1.0#state", ())]),
    ("i64_counter_ctl", WALK_SP + '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00\\04\\00\\00\\00\\08\\00\\00\\00")\n' + '  (func (export "anchor") (result i32) (i32.load (i32.const 0x2004)))\n' +
     '  (func (export "cnt") (result i32) (local i64)\n'
     '    (block (loop (br_if 1 (i64.ge_u (local.get 0) (i64.const 0x2008)))\n'
     '      (local.set 0 (i64.add (local.get 0) (i64.const 0x401))) (br 0)))\n'
     '    (i32.wrap_i64 (local.get 0))))',
     [("anchor", ()), ("cnt", ())]),
]

REFUSE = [
    ("datap_neg",
     '(module (memory 5376 (pagesize 1))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88\\04\\10\\00\\00")\n'
     + ANCHOR +
     '  (func (export "tbl") (result i32) (i32.load (i32.load (i32.const 0x1008)))))',
     [], ["npa-data-pointer (#1672)", "function 'tbl'", "load at op 1",
          "segment offset 0x8"]),
    ("str_neg",
     '(module (memory (export "mem") 1)\n'
     '  (data (i32.const 0x1000) "hello")\n'
     '  (data (i32.const 0x2000) "\\00\\10\\00\\00\\05\\00\\00\\00")\n'
     '  (func (export "first") (result i32) (i32.load8_u (i32.load (i32.const 0x2000)))))',
     [], ["npa-data-pointer (#1672)", "function 'first'", "load at op 1",
          "data segment 1", "segment offset 0x0"]),
    ("straddle_neg", SEG + ANCHOR +
     '  (func (export "f") (result i32) (i32.load (i32.add (i32.const 0xffe) (i32.const 0)))))',
     [], ["npa-region-straddle (#1604)", "function 'f'"]),
    ("fill_neg", SEG + ANCHOR +
     '  (func (export "f") (param i32)\n'
     '    (memory.fill (i32.add (i32.const 0xffc) (i32.const 0)) (i32.const 0xab) (local.get 0))))',
     [], ["npa-region-straddle (#1604)", "length computed at run time"]),
    ("below_sp_dyn",
     '(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x2000))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88")\n'
     '  (func (export "f") (param i32) (result i32) (i32.load offset=0x1004 (local.get 0))))',
     [], ["npa-dynamic-static-offset (#1568)", "function 'f'"]),
    # R1 boundary, the narrow refusal: an END pointer (one past segment 0)
    # COMPARED against a walked pointer — `while p != END` — would compare
    # against the start of the region holding END (the reservation here).
    # eab66646 compiled it and summed 0x1043 where wasmtime returns 0x3.
    ("end_cmp_neg",
     '(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x1000))\n'
     '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00")\n'
     '  (data (i32.const 0x3000) "\\40\\00\\00\\00")\n'
     '  (func (export "sum") (result i32) (local i32 i32)\n'
     '    (local.set 0 (i32.const 0x2000))\n'
     '    (block (loop\n'
     '      (br_if 1 (i32.eq (local.get 0) (i32.const 0x2008)))\n'
     '      (local.set 1 (i32.add (local.get 1) (i32.load (local.get 0))))\n'
     '      (local.set 0 (i32.add (local.get 0) (i32.const 4)))\n'
     '      (br 0)))\n'
     '    (local.get 1)))',
     [], ["npa-end-pointer-compare (#1604)", "function 'sum'", "0x2008"]),
    # The same refusal for the other comparison forms: `while p < END`
    # (eab66646 summed 0x1043), an i64 comparison of the extended end pointer
    # (0x1043), and an `i64.const` end (eab66646 faulted).
    ("end_ltu_neg", WALK_SP + WALK_SEG2
     + walk('(i32.eqz (i32.lt_u (local.get 0) (i32.const 0x2008)))'),
     [], ["npa-end-pointer-compare (#1604)", "function 'sum'", "0x2008"]),
    ("end_i64_neg", WALK_SP + WALK_SEG2
     + walk('(i64.eq (i64.extend_i32_u (local.get 0)) (i64.extend_i32_u (i32.const 0x2008)))'),
     [], ["npa-end-pointer-compare (#1604)", "function 'sum'", "0x2008"]),
    ("end_i64c_neg", WALK_SP + WALK_SEG2
     + walk('(i64.eq (i64.extend_i32_u (local.get 0)) (i64.const 0x2008))'),
     [], ["npa-end-pointer-compare (#1604)", "function 'sum'", "0x2008"]),
    # A counter compared with a constant equal to a segment end: on the split
    # layout every constant in the stack-pointer window is relocated, so
    # eab66646 compared the counter against a native address and never
    # stopped where wasmtime returns 8200. Refused by the same rule.
    ("end_scalar_neg", WALK_SP +
     '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00")\n'
     '  (func (export "anchor") (result i32) (i32.load (i32.const 0x2004)))\n'
     '  (func (export "cnt") (result i32) (local i32)\n'
     '    (block (loop (br_if 1 (i32.eq (local.get 0) (i32.const 0x2008)))\n'
     '      (local.set 0 (i32.add (local.get 0) (i32.const 0x401))) (br 0)))\n'
     '    (local.get 0)))',
     [], ["npa-end-pointer-compare (#1604)", "function 'cnt'", "0x2008"]),
    # #1684: an i64.const inside the static window compared with a pointer
    # derived from a static (eab66646 compiled it and faulted where wasmtime
    # returns 0x3), and one that reaches a memory-0 address (eab66646 refused
    # it for an unrelated reason, so this row is not a wrong-code control).
    ("i64_static_cmp_neg", WALK_SP + '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00\\04\\00\\00\\00\\08\\00\\00\\00")\n'
     + walk('(i64.eq (i64.extend_i32_u (local.get 0)) (i64.const 0x2008))'),
     [], ["npa-i64-static-const (#1684)", "function 'sum'", "0x2008"]),
    ("i64_static_addr_neg", WALK_SP + '  (data (i32.const 0x2000) "\\01\\00\\00\\00\\02\\00\\00\\00\\04\\00\\00\\00\\08\\00\\00\\00")\n' +
     '  (func (export "ld") (result i32) (i32.load (i32.wrap_i64 (i64.const 0x2004)))))',
     [], ["npa-i64-static-const (#1684)", "function 'ld'", "0x2004"]),
    # The data-pointer refusal still holds where it must: the same Location
    # dereference reached directly, and reached ONLY through call_indirect
    # (an elem function counts once a reachable function calls indirectly);
    # and a pointer TABLE read through a scaled index and dereferenced,
    # which eab66646 AND 257f0067 compiled and faulted on (wasmtime 97).
    ("gale_fp2a_direct_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (type $t (func (param i32) (result i32)))
  (table 2 funcref) (elem (i32.const 0) $fmt $pad)
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func $pad (param i32) (result i32) (i32.load8_u (i32.load (i32.const 0x84c))))
  (func $fmt (param i32) (result i32) (call_indirect (type $t) (local.get 0) (i32.const 1)))
  (func (export "anchor") (result i32) (i32.load8_u (i32.const 0x840)))
  (func (export "go") (result i32) (call $pad (i32.const 0))))""",
     [], ["npa-data-pointer (#1672)", "0x84c"]),
    ("gale_fp2a_indirect_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (type $t (func (param i32) (result i32)))
  (table 2 funcref) (elem (i32.const 0) $fmt $pad)
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func $pad (param i32) (result i32) (i32.load8_u (i32.load (i32.const 0x84c))))
  (func $fmt (param i32) (result i32) (call_indirect (type $t) (local.get 0) (i32.const 1)))
  (func (export "anchor") (result i32) (i32.load8_u (i32.const 0x840)))
  (func (export "go") (param i32) (result i32) (call_indirect (type $t) (i32.const 0) (local.get 0))))""",
     [], ["npa-data-pointer (#1672)", "0x84c"]),
    ("ptrtab_idx_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\61\62\63\00\78\79\7a\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x900) "\00\08\00\00\04\08\00\00")
  (func (export "name0") (param i32) (result i32)
    (i32.load8_u (i32.load offset=0x900 (i32.shl (local.get 0) (i32.const 2))))))""",
     [], ["npa-data-pointer (#1672)", "function 'name0'"]),
    # Still refused: the dead source made reachable through a reachable
    # call_indirect, and one of the two instances straddling its segment's
    # end (check(0x97c) reads up to 0x9b0, past [0x974, 0x9ad)).
    ("gale_fpA_indirect_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (type $t (func (param i32) (result i32)))
  (table 1 funcref) (elem (i32.const 0) $pad)
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x900) "\2a\00\00\00")
  (func $pad (param i32) (result i32)
    (i32.store (i32.sub (global.get $sp) (i32.const 16)) (i32.load (i32.const 0x84c)))
    (i32.const 0))
  (func (export "state") (result i32)
    (i32.store (i32.sub (global.get $sp) (i32.const 16)) (i32.const 0x900))
    (i32.load (i32.load (i32.sub (global.get $sp) (i32.const 16)))))
  (func (export "go") (param i32) (result i32) (call_indirect (type $t) (i32.const 0) (local.get 0))))""",
     [], ["npa-data-pointer (#1672)", "function 'state'"]),
    ("gale_fpB_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x938) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\01\01\00\00\02\01\00\00\03\01\00\00\04\01\00\00\05\01\00\00\06\01\00\00\07\01\00\00\08\01\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x974) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\01\02\00\00\02\02\00\00\03\02\00\00\04\02\00\00\05\02\00\00\06\02\00\00\07\02\00\00\08\02\00\00\00")
  (func $check (param i32) (result i32)
    (i32.add (i32.load offset=16 (local.get 0))
      (i32.add (i32.load offset=32 (local.get 0)) (i32.load offset=48 (local.get 0)))))
  (func (export "a") (result i32) (call $check (i32.const 0x938)))
  (func (export "b") (result i32) (call $check (i32.const 0x97c))))""",
     [], ["npa-region-straddle (#1604)"]),
    # Still refused: the same chain dereferenced in the Location caller's
    # own context; a true 4-byte straddle into the pointer-bearing segment;
    # the realloc shape under another name, with another signature; an
    # internal copy from a pointer-bearing constant; a copy from a param of
    # a NON-realloc export that may point at an escaped static (R3').
    ("gale_fpA1_ctx_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x1020) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\30\10\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x1188) "\00\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func $f60 (param i32 i32 i32) (result i32)
    (i32.add (i32.load (local.get 1)) (i32.mul (local.get 2) (i32.load (i32.add (local.get 1) (i32.const 128))))))
  (func $f61 (param i32 i32) (result i32)
    (call $f60 (i32.add (global.get $sp) (i32.const 8)) (local.get 0) (local.get 1)))
  (func (export "loc") (result i32) (i32.load8_u (call $f61 (i32.const 0x109c) (i32.const 0))))
  (func (export "run") (result i32)
    (i32.store (i32.const 0x1188) (i32.const 0x1030))
    (i32.load8_u (call $f61 (i32.const 4488) (i32.const 0)))))""",
     [], ["npa-data-pointer (#1672)", "function 'loc'"]),
    ("gale_fpA1_straddle_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x1020) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\30\10\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x1188) "\00\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func $f60 (param i32 i32 i32) (result i32)
    (i32.add (i32.load (local.get 1)) (i32.mul (local.get 2) (i32.load (i32.add (local.get 1) (i32.const 128))))))
  (func $f61 (param i32 i32) (result i32)
    (call $f60 (i32.add (global.get $sp) (i32.const 8)) (local.get 0) (local.get 1)))
  (func (export "run") (result i32)
    (i32.store (i32.const 0x1188) (i32.const 0x1030))
    (i32.load8_u (call $f61 (i32.const 4486) (i32.const 0)))))""",
     [], ["npa-region-straddle (#1604)"]),
    ("gale_fpA2_name_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x880) "hello\00\00\00")
  (func $impl (export "my_realloc") (param i32 i32 i32 i32) (result i32) (local i32)
    (local.set 4 (i32.add (i32.const 0xa00) (i32.load (i32.const 0x900))))
    (i32.store (i32.const 0x900) (i32.add (i32.load (i32.const 0x900)) (i32.const 16)))
    (if (local.get 0)
      (then (memory.copy (local.get 4) (local.get 0)
              (select (local.get 1) (local.get 3) (i32.lt_u (local.get 1) (local.get 3))))))
    (local.get 4))
  
  (func (export "loc") (result i32) (i32.const 0x84c))
  (func (export "run") (result i32) (local i32 i32)
    (local.set 0 (call $impl (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 0) (i32.const 0x880))
    (local.set 1 (call $impl (local.get 0) (i32.const 4) (i32.const 4) (i32.const 8)))
    (i32.load8_u (i32.load (local.get 1)))))""",
     [], ["npa-data-pointer (#1672)", "function 'run'"]),
    ("gale_fpA2_sig_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x880) "hello\00\00\00")
  (func $impl (export "cabi_realloc_wit_bindgen_0_52_0") (param i32 i32 i32) (result i32) (local i32)
    (local.set 3 (i32.add (i32.const 0xa00) (i32.load (i32.const 0x900))))
    (i32.store (i32.const 0x900) (i32.add (i32.load (i32.const 0x900)) (i32.const 16)))
    (if (local.get 0)
      (then (memory.copy (local.get 3) (local.get 0)
              (select (i32.const 4) (local.get 2) (i32.lt_u (i32.const 4) (local.get 2))))))
    (local.get 3))
  
  (func (export "loc") (result i32) (i32.const 0x84c))
  (func (export "run") (result i32) (local i32 i32)
    (local.set 0 (call $impl (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 0) (i32.const 0x880))
    (local.set 1 (call $impl (local.get 0) (i32.const 4) (i32.const 8)))
    (i32.load8_u (i32.load (local.get 1)))))""",
     [], ["npa-data-pointer (#1672)", "function 'run'"]),
    ("gale_fpA2_const_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func (export "run") (result i32)
    (memory.copy (i32.const 0xa00) (i32.const 0x84c) (i32.const 4))
    (i32.load8_u (i32.load (i32.const 0xa00)))))""",
     [], ["npa-data-pointer (#1672)", "function 'run'"]),
    ("gale_fpA2_r3_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\3f\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func (export "loc") (result i32) (i32.const 0x84c))
  (func (export "cp") (param i32 i32 i32 i32) (result i32)
    (memory.copy (i32.const 0xa00) (local.get 0) (i32.const 4))
    (i32.load8_u (i32.load (i32.const 0xa00)))))""",
     [], ["npa-data-pointer (#1672)", "function 'cp'"]),
    # Still refused: a pointer table read through a constant base in the
    # address plus a scaled index (R1 keeps the base's segment, which holds
    # pointers); a data pointer dereferenced with a small FIELD offset (not
    # a static memarg base); a realloc copy whose source may be old_ptr OR a
    # pointer-bearing constant (not an unchanged copy).
    ("gale_gf_ptrtab_site_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\61\62\63\00\78\79\7a\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x900) "\00\08\00\00\04\08\00\00")
  (func (export "name") (param i32) (result i32)
    (i32.load8_u (i32.load (i32.add (i32.const 0x900) (i32.shl (local.get 0) (i32.const 2)))))))""",
     [], ["npa-data-pointer (#1672)", "function 'name'"]),
    ("gale_gf_field_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x1000) "\08\10\00\00\00\00\00\00\07\00\00\00\09\00\00\00")
  (func (export "field") (result i32) (i32.load offset=4 (i32.load (i32.const 0x1000)))))""",
     [], ["npa-data-pointer (#1672)", "function 'field'"]),
    # The per-base rule applies only when each value IS its base (or base +
    # one unrelocated constant): a static base plus a choice of offsets that
    # crosses into the next segment keeps the union check, and refuses.
    ("gale_gf_union_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x938) "\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x974) "\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (func (export "pick") (param i32) (result i32)
    (i32.load (i32.add (i32.const 0x938) (select (i32.const 0) (i32.const 0x40) (local.get 0))))))""",
     [], ["npa-region-straddle (#1604)", "function 'pick'"]),
    ("gale_gfA2_mixed_neg", r"""(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x400))
  (data (i32.const 0x800) "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\73\72\63\2f\6c\69\62\2e\72\73\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\43\08\00\00\0a\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 0x8a0) "\68\65\6c\6c\6f\00\00\00\00\00\00\00\00\00\00\00")
  (func $realloc (export "cabi_realloc_wit_bindgen_0_52_0") (param i32 i32 i32 i32) (result i32) (local i32 i32 i32 i32 i32)
    (local.set 2 (i32.add (i32.const 2524) (i32.load offset=3548 (i32.const 0))))
    (i32.store offset=3548 (i32.const 0) (i32.add (i32.load offset=3548 (i32.const 0)) (i32.const 16)))
    (local.set 3 (select (local.get 3) (local.get 1) (i32.lt_u (local.get 3) (local.get 1))))
    (if (local.get 0) (then
      local.get 2
      (select (local.get 0) (i32.const 0x86c) (local.get 1))
      local.get 3
      local.set 7
      local.set 6
      local.set 5
      local.get 5
      local.get 6
      local.get 7
      memory.copy))
    (local.get 2))
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
    (call $realloc (local.get 0) (local.get 1) (local.get 2) (local.get 3)))
  (func (export "loc") (result i32) (i32.const 0x86c))
  (func (export "gust:sched/tasks@0.1.0#state") (result i32) (local i32 i32)
    (local.set 0 (call $realloc (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 0) (i32.const 0x8a0))
    (local.set 1 (call $realloc (local.get 0) (i32.const 4) (i32.const 4) (i32.const 8)))
    (i32.load8_u (i32.load (local.get 1)))))""",
     [], ["npa-data-pointer (#1672)"]),
    ("swb_neg", SEG + ANCHOR +
     '  (func (export "st0") (param i32 i32) (i32.store (local.get 0) (local.get 1))))',
     ["--safety-bounds", "software"], ["npa-software-bounds (#1661)", "function '"]),
]

MMIO = ('(module (memory 1)\n'
        '  (func (export "rd") (param i32) (result i32)\n'
        '    (i32.load (i32.add (i32.const 0x40000000) (local.get 0))))\n'
        '  (func (export "wr") (param i32 i32)\n'
        '    (i32.store (i32.add (i32.const 0x40000000) (local.get 0)) (local.get 1))))')


def compile_(wat, tmp, label, extra=()):
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


def execute(tmp, label, wat, seq):
    rc, log, obj = compile_(wat, tmp, label)
    if rc != 0:
        err = [ln for ln in log.splitlines() if ln.startswith("Error")]
        print(f"  [BUG] {label}: compile rc={rc}: {(err or [log[-300:]])[0][:300]}")
        return len(seq), 0
    linked = h.Linked(obj)
    cfg = wasmtime.Config()
    cfg.wasm_custom_page_sizes = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, wat), [])
    fails = 0
    for fn, args in seq:
        func = inst.exports(st)[fn]
        res = func(st, *args)
        got = linked.call(fn, args)
        if not func.type(st).results:
            ok, shown, exp = not isinstance(got, str), got if isinstance(got, str) else "(void)", "(void)"
        else:
            ok = not isinstance(got, str) and got[0] == res & 0xFFFFFFFF
            shown = got if isinstance(got, str) else hex(got[0])
            exp = hex(res & 0xFFFFFFFF)
        fails += not ok
        print(f"  [{'ok ' if ok else 'BUG'}] {label}.{fn}{args} -> {shown}  (wasmtime {exp})")
    return fails, len(seq)


def mmio(tmp):
    """R2: no data, no stack pointer — 0x40000000 + offset is native."""
    rc, log, obj = compile_(MMIO, tmp, "mmio_pos")
    if rc != 0:
        print(f"  [BUG] mmio_pos: compile rc={rc}: {log.strip().splitlines()[-1][:300]}")
        return 1, 0
    e = h.ELFFile(open(obj, "rb"))
    text = bytearray(e.get_section_by_name(".text").data())
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
    mu = h.Uc(h.UC_ARCH_ARM, h.UC_MODE_THUMB)
    mu.mem_map(h.BASES[".text"], h.MAPSZ)
    mu.mem_map(h.BASES[".bss"], h.MAPSZ)
    mu.mem_map(0x40000000, 0x1000)  # the peripheral page
    mu.mem_write(h.BASES[".text"], bytes(text))
    ret = h.BASES[".text"] + h.MAPSZ - 0x10
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.mem_write(0x40000010, (0xC0FFEE11).to_bytes(4, "little"))

    def call(fn, args):
        for reg, a in zip((h.UC_ARM_REG_R0, h.UC_ARM_REG_R1), args):
            mu.reg_write(reg, a)
        mu.reg_write(h.UC_ARM_REG_R11, 0)
        mu.reg_write(h.UC_ARM_REG_SP, h.BASES[".bss"] + h.MAPSZ - 0x100)
        mu.reg_write(h.UC_ARM_REG_LR, ret | 1)
        mu.emu_start((h.BASES[".text"] + syms[fn]) | 1, ret, timeout=2_000_000)
        return mu.reg_read(h.UC_ARM_REG_R0)

    fails = 0
    try:
        got = call("rd", (0x10,))
        ok = got == 0xC0FFEE11
        print(f"  [{'ok ' if ok else 'BUG'}] mmio_pos.rd(0x10) -> {got:#x} (native 0xc0ffee11)")
        fails += not ok
        call("wr", (0x20, 0x12345678))
        got = int.from_bytes(mu.mem_read(0x40000020, 4), "little")
        ok = got == 0x12345678
        print(f"  [{'ok ' if ok else 'BUG'}] mmio_pos.wr(0x20) -> {got:#x} at 0x40000020 (native 0x12345678)")
        fails += not ok
    except h.UcError as ex:
        print(f"  [BUG] mmio_pos: {ex}")
        return 1, 2
    return fails, 2


def main():
    tmp = Path(tempfile.mkdtemp(prefix="npa_model_"))
    fails = compared = 0
    print("=== executed rows ===")
    for label, wat, seq in EXEC:
        f, c = execute(tmp, label, wat, seq)
        fails += f
        compared += c
    print("=== R2: memory-mapped I/O in a module with no data (native contract) ===")
    f, c = mmio(tmp)
    fails += f
    compared += c
    print("=== refused rows ===")
    for label, wat, extra, needles in REFUSE:
        rc, log, obj = compile_(wat, tmp, label, extra)
        missing = [n for n in needles if n not in log]
        ok = rc != 0 and not missing and "panicked" not in log and not obj.exists()
        if not ok:
            fails += 1
        print(f"  [{'ok ' if ok else 'BUG'}] refused: {label} (rc={rc}"
              + (f", missing {missing}" if missing else "") + ")")
    floor = sum(len(s) for _, _, s in EXEC) + 2
    if compared < floor:
        print(f"VACUOUS: compared {compared} of {floor}")
        return 1
    print(f"\ncompared: {compared}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
