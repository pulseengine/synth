#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 500
"""RQ-91-MVDROP — an ARM function returns its wasm stack TOP, and a call
whose callee returns more than one result is REFUSED. Execution
differential against wasmtime, red-first.

THREE DEFECTS, all exit 0 with no diagnostic at d2094ca4. Found by the
IMAGEBUILDER sweep, which executed `tests/fixtures/multivalue_call_select/
control_call_drop.wat` for the first time: `call $two; drop` returned 20 where
wasm returns 10.

  D2 (the default path, single-value, no calls). The OPTIMIZED path (every
     self-contained cortex-m / cortex-r5 function without a local call)
     returned the last value PRODUCED, not the wasm stack top. `drop` emits no
     IR, and a store / `local.set` / `global.set` consumes without producing.
     So `x; y; drop` returned y, and the `mem::take` shape (load the old value,
     store 0) returned 0. An i64 `drop` popped ONE half of the pair (D2b).
     Fix: the optimized path declines such a function to the direct selector,
     which returns its operand stack's top.
  D1 (multi-result call). Both ARM selectors push ONE value per call, and the
     callee's unspecified multi-value convention leaves only its last result
     in R0 (#1450). A consumer that never underflows the short model — `drop`,
     `local.tee; drop`, an `if` arm, a forwarding function, `call_indirect` —
     compiled and returned the wrong value. Fix: REFUSED at
     `compile_wasm_to_arm` (needle below), as RV32 (#871) and aarch64 (#851)
     already refuse.
  D1c (void call_indirect). The #1210 void-callee rule covered `call` only; a
     VOID `call_indirect` pushed a phantom result (`i32.const 5; i32.const 0;
     call_indirect (type $void)` returned the callee's R0). Fix: no push.

LEGS (each case runs on the legs its shape reaches):
  m4, m3        self-contained Thumb image, booted through its Reset_Handler
                (the boot sweep's Image), optimized path
  m4-noopt      the same with --no-optimize (direct selector: the fallback target)
  r5            self-contained A32 image (optimized path), entered at the symbol
  m4-rel, r5-rel, m4-rel-fn   --relocatable objects (direct selector), linked
                with arm-none-eabi-ld; m4-rel-fn is --func-name
  m4f-rel       relocatable cortex-m4f, for the f32 multi-result call

GREEN (the default): every `value` cell equals live wasmtime at every vector,
and every `refuse` cell (a multi-result call) exits non-zero, not 101, with no
panic, no object written, and the needle. Every PINNED_WRONG value must still
differ from live wasmtime (the red table cannot go vacuous).

RED (`--red`, run with SYNTH = a d2094ca4 build): every cell is executed and
its value must EQUAL the PINNED_WRONG table exactly, in both directions. A
pinned cell that now returns wasmtime's value, or a wrong cell that is not
pinned, is a failure. The table was recorded from d2094ca4.

  SYNTH=./target/debug/synth python3 scripts/repro/stack_top_return_rq91_differential.py
  SYNTH=<d2094ca4 build>     python3 scripts/repro/stack_top_return_rq91_differential.py --red
"""

import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as ac

ROOT = Path(__file__).resolve().parents[2]
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
FIXTURES = ROOT / "tests/fixtures/multivalue_call_select"
NEEDLE = "MULTI-RESULT call"
M32 = 0xFFFFFFFF
VECTORS = (0, 1, 7, 0xFFFFFFFB)

_spec = importlib.util.spec_from_file_location(
    "boot", ROOT / "scripts/repro/self_contained_boot_sweep_1189_differential.py")
boot = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(boot)

LEGS = {
    "m4": (["--target", "cortex-m4", "--all-exports"], "image"),
    "m3": (["--target", "cortex-m3", "--all-exports"], "image"),
    "m4-noopt": (["--target", "cortex-m4", "--all-exports", "--no-optimize"], "image"),
    "r5": (["-b", "arm", "--target", "cortex-r5", "--all-exports"], "a32-image"),
    "m4-rel": (["--target", "cortex-m4", "--relocatable", "--all-exports"], "rel"),
    "r5-rel": (["-b", "arm", "--target", "cortex-r5", "--relocatable", "--all-exports"], "rel"),
    "m4-rel-fn": (["--target", "cortex-m4", "--relocatable", "--func-name", "@"], "rel"),
    "m4f-rel": (["--target", "cortex-m4f", "--relocatable", "--all-exports"], "rel"),
}
INT_LEGS = ("m4", "m3", "m4-noopt", "r5", "m4-rel", "r5-rel", "m4-rel-fn")
IMAGE_THUMB = ("m4", "m3", "m4-noopt")

HDR = """(module (memory 1) (global $g (mut i32) (i32.const 0))
  (func $two (result i32 i32) i32.const 10 i32.const 20)
  (func $three (result i32 i32 i32) i32.const 10 i32.const 20 i32.const 30)
  (func $twop (param i32) (result i32 i32) i32.const 10 i32.const 20)
  (func $i64two (result i64 i64) i64.const 0x100000000a i64.const 0x2000000014)
  (func $f32two (result f32 f32) f32.const 10.5 f32.const 20.25)
  (func $fwd (result i32 i32) call $two)
  (func $ret (result i32 i32) call $two return)
"""
# One-entry, homogeneous funcref tables (function 0), so the relocatable leg
# needs only the R11 table word the #642 oracle seeds, not a type-id sidecar.
CI_TWO = """(module (memory 1)
  (type $two (func (result i32 i32)))
  (table 1 funcref) (elem (i32.const 0) $t)
  (func $t (type $two) i32.const 10 i32.const 20)
  (func (export "f") (param i32) (result i32)
    i32.const 0 call_indirect (type $two) drop))
"""
CI_VOID = """(module (memory 1) (global $g (mut i32) (i32.const 0))
  (type $void (func))
  (table 1 funcref) (elem (i32.const 0) $v)
  (func $v (type $void) i32.const 77 global.set $g)
  (func (export "f") (param i32) (result i32)
    i32.const 5 i32.const 0 call_indirect (type $void)))
"""


def mod(body, result="i32", locals_=""):
    return HDR + f'  (func (export "f") (param i32) (result {result}) {locals_}\n    {body})\n)\n'


L = "(local i32) (local i64)"
# (case, wat, legs, branch mode). `refuse` = a multi-result call.
CASES = [
    # D2: the optimized epilogue (no calls)
    ("d2_const_drop", mod("i32.const 10 i32.const 20 drop"), INT_LEGS, "value"),
    ("d2_param_drop", mod("local.get 0 local.get 0 i32.const 1 i32.add drop"), INT_LEGS, "value"),
    ("d2_drop_const", mod("local.get 0 i32.const 7 drop"), INT_LEGS, "value"),
    ("d2_local_set", mod("local.get 0 i32.const 5 i32.add local.get 0 i32.const 9 i32.mul local.set 1", locals_=L), INT_LEGS, "value"),
    ("d2_global_set", mod("local.get 0 i32.const 1 i32.add local.get 0 i32.const 9 i32.mul global.set $g"), INT_LEGS, "value"),
    ("d2_store", mod("local.get 0 i32.const 1 i32.add i32.const 16 local.get 0 i32.const 9 i32.mul i32.store"), INT_LEGS, "value"),
    ("d2_tee_drop", mod("local.get 0 i32.const 1 i32.add local.get 0 i32.const 9 i32.mul local.tee 1 drop", locals_=L), INT_LEGS, "value"),
    ("d2_mem_take", mod("i32.const 16 local.get 0 i32.store i32.const 16 i32.load i32.const 16 i32.const 0 i32.store"), INT_LEGS, "value"),
    ("d2_block2_drop", mod("(block (result i32 i32) local.get 0 i32.const 20) drop"), INT_LEGS, "value"),
    ("d2b_i64_drop", mod("i64.const 0x100000000a i64.const 0x2000000014 drop i64.const 7 i64.rotl i32.wrap_i64"), INT_LEGS, "value"),
    ("d2b_i64_drop_ret", mod("local.get 0 i64.extend_i32_u i64.const 0x2000000014 drop", result="i64"), INT_LEGS, "value"),
    # D2 via a width mis-model: `local.set` of an i64 pops ONE slot, so the
    # pair's low half is left above the real result (spec local_set.wast's
    # `type-local-i64` takes this fallback; found by the home-alias audit's
    # function count moving)
    ("d2_i64_local_set", mod("local.get 0 i64.const 0x100000007 local.set 2", locals_=L), INT_LEGS, "value"),
    # D2 controls: the result IS the last value produced
    ("ctl_brif", mod("local.get 0 i32.const 1 i32.add local.get 0 i32.const 9 i32.mul br_if 0"), INT_LEGS, "value"),
    ("ctl_set_get", mod("local.get 0 i32.const 9 i32.mul local.set 1 local.get 1 i32.const 1 i32.add", locals_=L), INT_LEGS, "value"),
    ("ctl_block2_sub", mod("(block (result i32 i32) local.get 0 i32.const 2 i32.add local.get 0 i32.const 3 i32.mul) i32.sub"), INT_LEGS, "value"),
    # D1: multi-result calls (REFUSED on the branch)
    ("d1_call_drop", mod("call $two drop"), INT_LEGS, "refuse"),
    ("d1_call3_drop2", mod("call $three drop drop"), INT_LEGS, "refuse"),
    ("d1_call_tee", mod("call $two local.tee 1 drop", locals_=L), INT_LEGS, "refuse"),
    ("d1_param_call", mod("local.get 0 call $twop drop"), INT_LEGS, "refuse"),
    ("d1_forward", mod("call $fwd drop"), INT_LEGS, "refuse"),
    ("d1_return", mod("call $ret drop"), INT_LEGS, "refuse"),
    ("d1_if_arm", mod("local.get 0 (if (result i32 i32) (then i32.const 10 i32.const 20) (else call $two)) drop"), INT_LEGS, "refuse"),
    ("d1_i64_if_arm", mod("local.get 0 (if (result i64 i64) (then i64.const 0x100000000a i64.const 0x2000000014) (else call $i64two)) drop i64.const 7 i64.rotl i32.wrap_i64"), INT_LEGS, "refuse"),
    ("d1_call_indirect", CI_TWO, IMAGE_THUMB + ("m4-rel", "r5-rel"), "refuse"),
    ("d1_f32_if_arm", mod("local.get 0 (if (result f32 f32) (then f32.const 10.5 f32.const 20.25) (else call $f32two)) drop i32.reinterpret_f32"), ("m4f-rel",), "refuse"),
    # D1c: a void call_indirect pushes nothing (self-contained funcref table)
    ("d1c_void_call_indirect", CI_VOID, IMAGE_THUMB + ("m4-rel", "r5-rel", "m4-rel-fn"), "value"),
    # the #329/#330 fixtures, executed
    ("fx_control_call_drop", (FIXTURES / "control_call_drop.wat").read_text(), INT_LEGS, "refuse"),
    ("fx_repro_call_select", (FIXTURES / "repro_call_select.wat").read_text(), INT_LEGS, "refuse"),
    ("fx_control_block_select", (FIXTURES / "control_block_select.wat").read_text(), INT_LEGS, "value"),
    ("fx_control_single_call_select", (FIXTURES / "control_single_call_select.wat").read_text(), INT_LEGS, "value"),
]

# The RED half: what d2094ca4 RETURNED, per (case, leg) -> {arg: value}.
# Recorded with `--red --dump` against a d2094ca4 release build. Values are
# 32-bit words (an i64 result is (lo, hi)), only the vectors that were wrong;
# a cell that was right on every vector, or declined, at d2094ca4 is absent.
# 111 cells: D2 on the three optimized-path legs (m4, m3, r5), D1 on every
# ARM leg that compiled it, D1c on every leg with a funcref table. Canary
# values name what was returned: 0xFEEDFACE / 0xC0DE000n are untouched
# argument registers, 77 is the void callee's R0.
PINNED_WRONG = {
    ('d2_i64_local_set', 'm3'): {0: (7,), 1: (7,), 4294967291: (7,)},
    ('d2_i64_local_set', 'm4'): {0: (7,), 1: (7,), 4294967291: (7,)},
    ('d2_i64_local_set', 'r5'): {0: (7,), 1: (7,), 4294967291: (7,)},
    ('d1_call3_drop2', 'm3'): {0: (30,), 1: (30,), 7: (30,), 4294967291: (30,)},
    ('d1_call3_drop2', 'm4'): {0: (30,), 1: (30,), 7: (30,), 4294967291: (30,)},
    ('d1_call3_drop2', 'm4-noopt'): {0: (30,), 1: (30,), 7: (30,), 4294967291: (30,)},
    ('d1_call3_drop2', 'm4-rel'): {0: (30,), 1: (30,), 7: (30,), 4294967291: (30,)},
    ('d1_call3_drop2', 'm4-rel-fn'): {0: (30,), 1: (30,), 7: (30,), 4294967291: (30,)},
    ('d1_call3_drop2', 'r5'): {0: (30,), 1: (30,), 7: (30,), 4294967291: (30,)},
    ('d1_call3_drop2', 'r5-rel'): {0: (30,), 1: (30,), 7: (30,), 4294967291: (30,)},
    ('d1_call_drop', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_drop', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_drop', 'm4-noopt'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_drop', 'm4-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_drop', 'm4-rel-fn'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_drop', 'r5'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_drop', 'r5-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_indirect', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_indirect', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_indirect', 'm4-noopt'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_indirect', 'm4-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_indirect', 'r5-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_call_tee', 'm3'): {0: (0,), 1: (1,), 7: (7,), 4294967291: (4294967291,)},
    ('d1_call_tee', 'm4'): {0: (0,), 1: (1,), 7: (7,), 4294967291: (4294967291,)},
    ('d1_call_tee', 'm4-noopt'): {0: (0,), 1: (1,), 7: (7,), 4294967291: (4294967291,)},
    ('d1_call_tee', 'm4-rel'): {0: (0,), 1: (1,), 7: (7,), 4294967291: (4294967291,)},
    ('d1_call_tee', 'm4-rel-fn'): {0: (0,), 1: (1,), 7: (7,), 4294967291: (4294967291,)},
    ('d1_call_tee', 'r5'): {0: (0,), 1: (1,), 7: (7,), 4294967291: (4294967291,)},
    ('d1_call_tee', 'r5-rel'): {0: (0,), 1: (1,), 7: (7,), 4294967291: (4294967291,)},
    ('d1_f32_if_arm', 'm4f-rel'): {0: (1101135872,)},
    ('d1_forward', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_forward', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_forward', 'm4-noopt'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_forward', 'm4-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_forward', 'm4-rel-fn'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_forward', 'r5'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_forward', 'r5-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_i64_if_arm', 'm3'): {0: (1996318591,)},
    ('d1_i64_if_arm', 'm4'): {0: (1996318591,)},
    ('d1_i64_if_arm', 'm4-noopt'): {0: (2560,)},
    ('d1_i64_if_arm', 'm4-rel'): {0: (2560,)},
    ('d1_i64_if_arm', 'm4-rel-fn'): {0: (2560,)},
    ('d1_i64_if_arm', 'r5'): {0: (1862271328,)},
    ('d1_i64_if_arm', 'r5-rel'): {0: (2560,)},
    ('d1_if_arm', 'm3'): {0: (4277009102,)},
    ('d1_if_arm', 'm4'): {0: (4277009102,)},
    ('d1_if_arm', 'm4-noopt'): {0: (4277009102,)},
    ('d1_if_arm', 'm4-rel'): {0: (3235774466,)},
    ('d1_if_arm', 'm4-rel-fn'): {0: (3235774466,)},
    ('d1_if_arm', 'r5'): {0: (3235774466,)},
    ('d1_if_arm', 'r5-rel'): {0: (3235774466,)},
    ('d1_param_call', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_param_call', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_param_call', 'm4-noopt'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_param_call', 'm4-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_param_call', 'm4-rel-fn'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_param_call', 'r5'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_param_call', 'r5-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_return', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_return', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_return', 'm4-noopt'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_return', 'm4-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_return', 'm4-rel-fn'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_return', 'r5'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1_return', 'r5-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d1c_void_call_indirect', 'm3'): {0: (77,), 1: (77,), 7: (77,), 4294967291: (77,)},
    ('d1c_void_call_indirect', 'm4'): {0: (77,), 1: (77,), 7: (77,), 4294967291: (77,)},
    ('d1c_void_call_indirect', 'm4-noopt'): {0: (77,), 1: (77,), 7: (77,), 4294967291: (77,)},
    ('d1c_void_call_indirect', 'm4-rel'): {0: (77,), 1: (77,), 7: (77,), 4294967291: (77,)},
    ('d1c_void_call_indirect', 'm4-rel-fn'): {0: (77,), 1: (77,), 7: (77,), 4294967291: (77,)},
    ('d1c_void_call_indirect', 'r5-rel'): {0: (77,), 1: (77,), 7: (77,), 4294967291: (77,)},
    ('d2_block2_drop', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d2_block2_drop', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d2_block2_drop', 'r5'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d2_const_drop', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d2_const_drop', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d2_const_drop', 'r5'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('d2_drop_const', 'm3'): {0: (7,), 1: (7,), 4294967291: (7,)},
    ('d2_drop_const', 'm4'): {0: (7,), 1: (7,), 4294967291: (7,)},
    ('d2_drop_const', 'r5'): {0: (7,), 1: (7,), 4294967291: (7,)},
    ('d2_global_set', 'm3'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_global_set', 'm4'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_global_set', 'r5'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_local_set', 'm3'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_local_set', 'm4'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_local_set', 'r5'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_mem_take', 'm3'): {1: (0,), 7: (0,), 4294967291: (0,)},
    ('d2_mem_take', 'm4'): {1: (0,), 7: (0,), 4294967291: (0,)},
    ('d2_mem_take', 'r5'): {1: (0,), 7: (0,), 4294967291: (0,)},
    ('d2_param_drop', 'm3'): {0: (1,), 1: (2,), 7: (8,), 4294967291: (4294967292,)},
    ('d2_param_drop', 'm4'): {0: (1,), 1: (2,), 7: (8,), 4294967291: (4294967292,)},
    ('d2_param_drop', 'r5'): {0: (1,), 1: (2,), 7: (8,), 4294967291: (4294967292,)},
    ('d2_store', 'm3'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_store', 'm4'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_store', 'r5'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_tee_drop', 'm3'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_tee_drop', 'm4'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2_tee_drop', 'r5'): {0: (0,), 1: (9,), 7: (63,), 4294967291: (4294967251,)},
    ('d2b_i64_drop', 'm3'): {0: (2048,), 1: (2048,), 7: (2048,), 4294967291: (2048,)},
    ('d2b_i64_drop', 'm4'): {0: (2048,), 1: (2048,), 7: (2048,), 4294967291: (2048,)},
    ('d2b_i64_drop', 'r5'): {0: (2048,), 1: (2048,), 7: (2048,), 4294967291: (2048,)},
    ('d2b_i64_drop_ret', 'm3'): {0: (20, 32), 1: (20, 32), 7: (20, 32), 4294967291: (20, 32)},
    ('d2b_i64_drop_ret', 'm4'): {0: (20, 32), 1: (20, 32), 7: (20, 32), 4294967291: (20, 32)},
    ('d2b_i64_drop_ret', 'r5'): {0: (20, 32), 1: (20, 32), 7: (20, 32), 4294967291: (20, 32)},
    ('fx_control_call_drop', 'm3'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('fx_control_call_drop', 'm4'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('fx_control_call_drop', 'm4-noopt'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('fx_control_call_drop', 'm4-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('fx_control_call_drop', 'm4-rel-fn'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('fx_control_call_drop', 'r5'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
    ('fx_control_call_drop', 'r5-rel'): {0: (20,), 1: (20,), 7: (20,), 4294967291: (20,)},
}

TEXT_BASE, MEM_BASE, STK = 0x10000, 0x20000000, 0x30000000
TABLE_FUNCS = (0,)  # CI_TWO / CI_VOID: `(elem (i32.const 0) <function 0>)`
RET = STK + 0xF000
EMU = 0


def need(tool):
    p = shutil.which(tool)
    if p is None:
        sys.exit(f"FAIL: {tool} not found — a skipped link is a vacuous gate")
    return p


def wasm_truth(wat, arg):
    """-> (result words,) from live wasmtime; an i64 result is (lo, hi)."""
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, wat), [])
    f = inst.exports(st)["f"]
    a = [boot.to_signed(arg, 32)] if f.type(st).params else []
    v = f(st, *a)
    if [str(t) for t in f.type(st).results] == ["i64"]:
        return (v & M32, (v >> 32) & M32)
    return (v & M32,)


def compile_cell(wat, leg, tmp):
    flags = ["f" if x == "@" else x for x in LEGS[leg][0]]
    src = Path(tmp) / "in.wat"
    src.write_text(wat)
    out = Path(tmp) / f"{leg}.o"
    if out.exists():
        out.unlink()
    r = subprocess.run([SYNTH, "compile", str(src), *flags, "-o", str(out)],
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr, out


def load_sections(path):
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        st = next(s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        syms = {s.name: s["st_value"] for s in st.iter_symbols()
                if s.name and s["st_shndx"] != "SHN_UNDEF"}
        secs = [(s["sh_addr"], s["sh_size"], s.data() if s["sh_type"] != "SHT_NOBITS" else b"")
                for s in e.iter_sections() if s["sh_flags"] & 2 and s["sh_size"]]
    return syms, secs


def run_sections(path, arg, words):
    """Enter `f` of a linked object / A32 image at its symbol."""
    global EMU
    syms, secs = load_sections(path)
    addr = syms["f"]
    thumb = addr & 1
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
    pages = {pg for va, sz, _ in secs
             for pg in range(va & ~0xFFF, (va + sz + 0xFFF) & ~0xFFF, 0x1000)}
    for pg in sorted(pages):
        mu.mem_map(pg, 0x1000)
    for va, _, d in secs:
        if d:
            mu.mem_write(va, d)
    for base in (MEM_BASE, STK):
        if not any(base <= pg < base + 0x10000 for pg in pages):
            mu.mem_map(base, 0x10000)
    try:
        mu.reg_write(ac.UC_ARM_REG_C1_C0_2, mu.reg_read(ac.UC_ARM_REG_C1_C0_2) | (0xF << 20))
        mu.reg_write(ac.UC_ARM_REG_FPEXC, 0x40000000)
    except UcError:
        pass
    # The --relocatable funcref table lives at R11 (the embedder contract the
    # #642 oracle seeds the same way): the call_indirect cases' one-entry
    # table holds function 0, entered by its linked address.
    for slot, fidx in enumerate(TABLE_FUNCS):
        if f"func_{fidx}" in syms:
            mu.mem_write(MEM_BASE + 4 * slot, (syms[f"func_{fidx}"]).to_bytes(4, "little"))
    mu.reg_write(ac.UC_ARM_REG_SP, RET - 0x100)
    mu.reg_write(ac.UC_ARM_REG_LR, RET | thumb)
    mu.reg_write(ac.UC_ARM_REG_R0, arg)
    for i, r in enumerate((ac.UC_ARM_REG_R1, ac.UC_ARM_REG_R2, ac.UC_ARM_REG_R3, ac.UC_ARM_REG_R12)):
        mu.reg_write(r, 0xC0DE0001 + i)  # a stale-register return names itself
    mu.reg_write(ac.UC_ARM_REG_R9, MEM_BASE)
    mu.reg_write(ac.UC_ARM_REG_R10, 0x10000)
    mu.reg_write(ac.UC_ARM_REG_R11, MEM_BASE)
    EMU += 1
    try:
        mu.emu_start(addr | thumb if thumb else addr, RET, count=200_000)
    except UcError as e:
        return f"fault:{e}"
    if mu.reg_read(ac.UC_ARM_REG_PC) & ~1 != RET:
        return "timeout"
    return tuple(mu.reg_read(r) & M32 for r in (ac.UC_ARM_REG_R0, ac.UC_ARM_REG_R1)[:words])


def execute(out, kind, words, tmp):
    """-> {arg: tuple-or-str}"""
    global EMU
    if kind == "image":
        img = boot.Image(out)
        if img.boot != "ok":
            return {a: f"boot:{img.boot}" for a in VECTORS}
        res = {}
        for a in VECTORS:
            EMU += 1
            got, _viol = img.call("f", [a], words)
            res[a] = tuple(got[1]) if got[0] == "ok" else got[0]
        return res
    exe = out
    if kind == "rel":
        exe = Path(tmp) / "linked.elf"
        r = subprocess.run([need("arm-none-eabi-ld"), "-e", "f", f"-Ttext={TEXT_BASE:#x}",
                            str(out), "-o", str(exe)], capture_output=True, text=True)
        if r.returncode:
            return {a: f"link:{r.stderr.strip()[:80]}" for a in VECTORS}
    return {a: run_sections(exe, a, words) for a in VECTORS}


def main():
    red = "--red" in sys.argv[1:]
    need("arm-none-eabi-ld")
    fails, compared, refused = [], 0, 0
    observed_wrong = {}
    for case, wat, legs, mode in CASES:
        want = {a: wasm_truth(wat, a) for a in VECTORS}
        words = len(want[VECTORS[0]])
        for leg in legs:
            with tempfile.TemporaryDirectory() as tmp:
                rc, log, out = compile_cell(wat, leg, tmp)
                if mode == "refuse" and not red:
                    ok = (rc not in (0, 101) and NEEDLE in log and "panicked" not in log
                          and not out.exists())
                    refused += 1
                    print(f"  [refuse] {case:30} {leg:9} {'refused' if ok else 'NOT REFUSED'}")
                    if not ok:
                        fails.append(f"{case}/{leg}: expected a {NEEDLE!r} refusal, rc={rc}")
                    continue
                if rc != 0 or not out.exists():
                    if red and (case, leg) not in PINNED_WRONG:
                        continue  # declined at d2094ca4 too: nothing to pin
                    fails.append(f"{case}/{leg}: compile failed rc={rc}: {log.strip()[-160:]}")
                    continue
                got = execute(out, LEGS[leg][1], words, tmp)
            bad = {a: got[a] for a in VECTORS if got[a] != want[a]}
            compared += len(VECTORS)
            if bad:
                observed_wrong[(case, leg)] = bad
            if red:
                continue
            print(f"  [value]  {case:30} {leg:9} {'ok' if not bad else 'WRONG ' + str(bad)}")
            if bad:
                fails.append(f"{case}/{leg}: {bad} (wasmtime {want})")
    if red:
        for key in sorted(set(PINNED_WRONG) | set(observed_wrong)):
            if PINNED_WRONG.get(key) != observed_wrong.get(key):
                fails.append(f"RED {key}: pinned {PINNED_WRONG.get(key)} observed {observed_wrong.get(key)}")
        if "--dump" in sys.argv[1:]:
            print("PINNED_WRONG = {")
            for key in sorted(observed_wrong):
                print(f"    {key!r}: {observed_wrong[key]!r},")
            print("}")
        print(f"RQ-91-MVDROP RED: {len(observed_wrong)} wrong cells observed, "
              f"{len(PINNED_WRONG)} pinned, {compared} values compared")
    else:
        # The red table stays non-vacuous: each pinned value differs from live wasmtime.
        for (case, leg), cells in PINNED_WRONG.items():
            wat = next(w for c, w, _l, _m in CASES if c == case)
            for a, v in cells.items():
                if v == wasm_truth(wat, a):
                    fails.append(f"PINNED_WRONG {case}/{leg} arg {a}: equals wasmtime — vacuous")
        print(f"RQ-91-MVDROP: {compared} values compared, {refused} refusals, "
              f"{EMU} emulator entries, {len(fails)} failure(s)")
    for f in fails:
        print(f"  FAIL {f}")
    if not red and EMU == 0:
        fails.append("no emulation ran")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
