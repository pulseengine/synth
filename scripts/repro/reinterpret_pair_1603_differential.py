#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 2512
"""#1603 (RQ-89-REINTERP) — EXECUTE the f64<->i64 bit-casts
(`i64.reinterpret_f64`, `f64.reinterpret_i64`) on cortex-m7dp against
wasmtime, in every position the converted value can flow to.

# The defect

On the direct selector (`select_with_stack` — the only ARM path that lowers
f64; the optimized path bails to it for every float op), neither bit-cast had
a stack-aware lowering: both were missing from `is_scope_f64_op` and from
`try_lower_f64`, so they fell to the main match's `_ =>` arm, which calls the
REGISTER-BLIND `select_default`. That arm moved a D-register picked by its own
counter (not the operand's) into core registers picked by its own allocator,
then pushed an unrelated i32-tagged placeholder register. Shipped v0.88.0
output for `(i64.reinterpret_f64 (f64.load (local.get 0)))` as the function
result: `vmov r3, r4, d0` then `mov r0, r5` — r5 never written, r1 untouched.
rc=0, garbage returned.

# What this oracle does

Compiles the inline module below (no .wat fixture, so the corpus-wide audit
populations do not grow) for cortex-m7dp — the only double-precision ARM
target — `--relocatable` AND self-contained, plus a single-precision control
(cortex-m7, which must DECLINE every f64 export loudly and compile the f32
controls). Every export is run under unicorn (ELF symtab, local BLs resolved
from `.rel.text`) against wasmtime in two machine states: ZEROED registers +
stack, and GARBAGE core/VFP registers + a garbage stack — the state that
exposes a result read from a register nothing wrote (the #1603 `mov r0, r5`).

Positions covered, for BOTH directions (`ri_*` = i64.reinterpret_f64,
`rf_*` = f64.reinterpret_i64): function result (from a param, the second
param, a load, arithmetic, a constant, a call result), call argument, stored
to memory, i64/f64 arithmetic, comparison, i64 local across a block, `if`
result, `br_if` value, select, loop accumulation, two live casts at once,
round trips, plus f32<->i32 bit-casts as the already-correct control.

The SAME width model fed a second, older defect in this class:
`infer_i64_locals` (which decides whether a non-param local is 8 bytes) did
not count ANY float->i64 producer as 64-bit, so an i64 local written from
`i64.reinterpret_f64` or `i64.trunc{,_sat}_f{32,64}_{s,u}` was inferred i32
and promoted to a single register — upper word dropped. The `*_local*` and
`tr_*` rows cover it, including cortex-m7's #1069 AEABI route (the builtin
is a Python stub that clobbers every caller-saved register).

Four positions are refused for reasons that a plain value of the same type
hits identically (see EXPECTED_DECLINES); the oracle fails if one starts
compiling, so it is then executed here.

Red-first (measured on origin/main 7e170d62, the pre-fix selector): every
`ri_*` position that compiled returned a wrong value (1 compile was the #929
i64-argument shape that only compiled BECAUSE the cast was mis-typed i32),
every `rf_*` position except the round trip DECLINED (the placeholder was
i32-tagged, so the next f64 consumer refused), `rt_ifi` was silently wrong,
and the four `*_local*`/`tr_*` rows were wrong — 1128 failures over 1652
emulations. Fixed: 2512 of 2512 bit-identical.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/reinterpret_pair_1603_differential.py
  (--map prints the per-export table and exits 0 regardless — class mapping)
"""

import os
import random
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as A

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
MAP = "--map" in sys.argv

# name -> (params, result, body). Helpers (h_*) are exported so they are
# compiled and callable; they are executed like any other export.
FUNCS = {
    # -- helpers -----------------------------------------------------------
    "h_negf64": (["f64"], "f64", "(f64.neg (local.get 0))"),
    "h_inc64": (["i64"], "i64", "(i64.add (local.get 0) (i64.const 1))"),
    "h_ld64": (["i32"], "i64", "(i64.load offset=8 (local.get 0))"),
    "h_wordsum": (["f64"], "i32",
                  "(i32.add (i32.wrap_i64 (i64.reinterpret_f64 (local.get 0)))"
                  " (i32.wrap_i64 (i64.shr_u (i64.reinterpret_f64 (local.get 0))"
                  " (i64.const 32))))"),
    # -- i64.reinterpret_f64 ----------------------------------------------
    "ri_ret_load": (["i32"], "i64",
                    "(i64.reinterpret_f64 (f64.load (local.get 0)))"),
    "ri_ret_param": (["f64"], "i64", "(i64.reinterpret_f64 (local.get 0))"),
    "ri_ret_param2": (["f64", "f64"], "i64",
                      "(i64.reinterpret_f64 (local.get 1))"),
    "ri_ret_arith": (["f64", "f64"], "i64",
                     "(i64.reinterpret_f64 (f64.mul (local.get 0) (local.get 1)))"),
    "ri_ret_const": (["i32"], "i64",
                     "(i64.reinterpret_f64 (f64.const -0x1.23456789abcdep+700))"),
    "ri_ret_call": (["f64"], "i64",
                    "(i64.reinterpret_f64 (call $h_negf64 (local.get 0)))"),
    "ri_add": (["f64", "i64"], "i64",
               "(i64.add (i64.reinterpret_f64 (local.get 0)) (local.get 1))"),
    "ri_hiword": (["f64"], "i32",
                  "(i32.wrap_i64 (i64.shr_u (i64.reinterpret_f64 (local.get 0))"
                  " (i64.const 32)))"),
    "ri_eq": (["f64", "i64"], "i32",
              "(i64.eq (i64.reinterpret_f64 (local.get 0)) (local.get 1))"),
    "ri_lt": (["f64", "i64"], "i32",
              "(i64.lt_s (i64.reinterpret_f64 (local.get 0)) (local.get 1))"),
    "ri_store": (["i32", "f64"], "i64",
                 "(i64.store (local.get 0) (i64.reinterpret_f64 (local.get 1)))"
                 " (i64.load (local.get 0))"),
    "ri_store_hi": (["i32", "f64"], "i32",
                    "(i64.store (local.get 0) (i64.reinterpret_f64 (local.get 1)))"
                    " (i32.load offset=4 (local.get 0))"),
    "ri_local": (["f64"], "i64",
                 "(local $t i64) (local.set $t (i64.reinterpret_f64 (local.get 0)))"
                 " (block (nop)) (i64.xor (local.get $t) (i64.const 0x5555))"),
    "ri_if": (["f64", "i32"], "i64",
              "(if (result i64) (local.get 1)"
              " (then (i64.reinterpret_f64 (local.get 0)))"
              " (else (i64.const 7)))"),
    "ri_br": (["f64", "i32"], "i64",
              "(block (result i64) (i64.reinterpret_f64 (local.get 0))"
              " (local.get 1) (br_if 0) (drop) (i64.const 9))"),
    "ri_select": (["f64", "f64", "i32"], "i64",
                  "(select (i64.reinterpret_f64 (local.get 0))"
                  " (i64.reinterpret_f64 (local.get 1)) (local.get 2))"),
    "ri_two": (["f64", "f64"], "i64",
               "(i64.sub (i64.reinterpret_f64 (local.get 0))"
               " (i64.reinterpret_f64 (local.get 1)))"),
    "ri_loop": (["f64", "i32"], "i64",
                "(local $acc i64) (local $n i32)"
                " (local.set $n (i32.and (local.get 1) (i32.const 3)))"
                " (block (loop (br_if 1 (i32.eqz (local.get $n)))"
                " (local.set $acc (i64.add (local.get $acc)"
                " (i64.reinterpret_f64 (local.get 0))))"
                " (local.set $n (i32.sub (local.get $n) (i32.const 1)))"
                " (br 0)))"
                " (local.get $acc)"),
    "ri_local_tee": (["f64"], "i64",
                     "(local $t i64) (drop (local.tee $t (i64.reinterpret_f64 (local.get 0))))"
                     " (block (nop)) (i64.rotl (local.get $t) (i64.const 7))"),
    # the same i64-local width model (`infer_i64_locals`) serves every
    # float->i64 producer; the trunc_sat family rides the same rows.
    "tr_local": (["f64"], "i64",
                 "(local $t i64) (local.set $t (i64.trunc_sat_f64_s (local.get 0)))"
                 " (block (nop)) (i64.xor (local.get $t) (i64.const 0x5555))"),
    "tr_local_f32": (["f32"], "i64",
                     "(local $t i64) (local.set $t (i64.trunc_sat_f32_u (local.get 0)))"
                     " (block (nop)) (i64.xor (local.get $t) (i64.const 0x5555))"),
    "ri_call_arg": (["f64"], "i64",
                    "(call $h_inc64 (i64.reinterpret_f64 (local.get 0)))"),
    # -- f64.reinterpret_i64 ----------------------------------------------
    "rf_ret_param": (["i64"], "f64", "(f64.reinterpret_i64 (local.get 0))"),
    "rf_ret_param2": (["i64", "i64"], "f64",
                      "(f64.reinterpret_i64 (local.get 1))"),
    "rf_ret_load": (["i32"], "f64",
                    "(f64.reinterpret_i64 (i64.load (local.get 0)))"),
    "rf_ret_intarith": (["i64", "i64"], "f64",
                        "(f64.reinterpret_i64 (i64.add (local.get 0) (local.get 1)))"),
    "rf_ret_const": (["i32"], "f64",
                     "(f64.reinterpret_i64 (i64.const 0x7ff8000000000123))"),
    "rf_ret_call": (["i32"], "f64",
                    "(f64.reinterpret_i64 (call $h_ld64 (local.get 0)))"),
    "rf_arith": (["i64", "f64"], "f64",
                 "(f64.add (f64.reinterpret_i64 (local.get 0)) (local.get 1))"),
    "rf_eq": (["i64", "f64"], "i32",
              "(f64.eq (f64.reinterpret_i64 (local.get 0)) (local.get 1))"),
    "rf_store": (["i32", "i64"], "f64",
                 "(f64.store (local.get 0) (f64.reinterpret_i64 (local.get 1)))"
                 " (f64.load (local.get 0))"),
    "rf_store_lo": (["i32", "i64"], "i32",
                    "(f64.store (local.get 0) (f64.reinterpret_i64 (local.get 1)))"
                    " (i32.load (local.get 0))"),
    "rf_local": (["i64"], "f64",
                 "(local $t f64) (local.set $t (f64.reinterpret_i64 (local.get 0)))"
                 " (block (nop)) (f64.neg (local.get $t))"),
    "rf_if": (["i64", "i32"], "f64",
              "(if (result f64) (local.get 1)"
              " (then (f64.reinterpret_i64 (local.get 0)))"
              " (else (f64.const 2.5)))"),
    "rf_br": (["i64", "i32"], "f64",
              "(block (result f64) (f64.reinterpret_i64 (local.get 0))"
              " (local.get 1) (br_if 0) (drop) (f64.const -4.25))"),
    "rf_select": (["i64", "i32"], "f64",
                  "(select (f64.reinterpret_i64 (local.get 0))"
                  " (f64.reinterpret_i64 (i64.rotl (local.get 0) (i64.const 13)))"
                  " (local.get 1))"),
    "rf_call_arg": (["i64"], "i32",
                    "(call $h_wordsum (f64.reinterpret_i64 (local.get 0)))"),
    "rf_call_argf": (["i64"], "f64",
                     "(call $h_negf64 (f64.reinterpret_i64 (local.get 0)))"),
    # -- round trips ------------------------------------------------------
    "rt_fif": (["f64"], "f64",
               "(f64.reinterpret_i64 (i64.reinterpret_f64 (local.get 0)))"),
    "rt_ifi": (["i64"], "i64",
               "(i64.reinterpret_f64 (f64.reinterpret_i64 (local.get 0)))"),
    "rt_ifi_neg": (["i64"], "i64",
                   "(i64.reinterpret_f64 (f64.neg (f64.reinterpret_i64 (local.get 0))))"),
    # -- f32 <-> i32 controls ---------------------------------------------
    "c32_ret": (["f32"], "i32", "(i32.reinterpret_f32 (local.get 0))"),
    "c32_retf": (["i32"], "f32", "(f32.reinterpret_i32 (local.get 0))"),
    "c32_add": (["f32", "i32"], "i32",
                "(i32.add (i32.reinterpret_f32 (local.get 0)) (local.get 1))"),
    "c32_addf": (["i32", "f32"], "f32",
                 "(f32.add (f32.reinterpret_i32 (local.get 0)) (local.get 1))"),
}

# Exports refused on cortex-m7dp for a reason OTHER than #1603 — a loud
# decline (reach, not wrongness) that a plain, non-bit-cast value of the same
# type hits identically — pinned so a change in either direction is seen:
#   #929  an i64 call ARGUMENT is not marshalled as a register pair;
#   #509  an i64 value carried over br/br_if/br_table;
#   #313  an f64 `if` result (even `f64.neg` of a param declines the same);
#   #1318 an f64 value carried over br/br_if/br_table.
EXPECTED_DECLINES = {"ri_call_arg": "#929", "ri_br": "#509", "rf_if": "#313",
                     "rf_br": "#1318"}

F64_BITS = [0x3FF8000000000000, 0xC00921FB54442D18, 0x8000000000000000,
            0x0000000000000001, 0x7FF0000000000000, 0x7FF8000000000123,
            0x123456789ABCDEF0, 0xFFFFFFFF00000001, 0xC2F0000000000123]
F32_BITS = [0x3FC00000, 0xC0490FDB, 0x80000000, 0x00000001, 0x7FC00123, 0x5F000001]
I32_V = [0, 1, 6]
ADDR_V = [64, 1000]
CONFIGS = [("cortex-m7dp", True), ("cortex-m7dp", False), ("cortex-m7", True)]
STK, STKSZ = 0x300000, 0x10000
SP0 = STK + STKSZ - 0x100
RET = 0x400000
STUB = 0x500000
MEM = 0x20000000


def _f2lz(signed):
    def run(r0, _r1):
        x = struct.unpack("<f", struct.pack("<I", r0))[0]
        v = int(x)  # the caller guards NaN / out-of-range before the call
        return v & M64
    return run


# AEABI run-time builtins a single-precision `--relocatable` object may call
# (#1069). Only the f32 -> i64 truncations are reachable from this module.
AEABI = {"__aeabi_f2lz": _f2lz(True), "__aeabi_f2ulz": _f2lz(False)}
M64 = (1 << 64) - 1


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def module_wat():
    out = ["(module (memory (export \"mem\") 1)"]
    for name, (params, res, body) in FUNCS.items():
        ps = " ".join(f"(param {p})" for p in params)
        out.append(f"  (func ${name} (export \"{name}\") {ps} (result {res}) {body})")
    out.append(")")
    return "\n".join(out)


def mem_image():
    rng = random.Random(0x1603)
    return bytes(rng.getrandbits(8) for _ in range(2048))


def arg_vectors(params, body):
    is_mem = "load" in body or "store" in body
    pools = []
    for p in params:
        if p in ("f64", "i64"):
            pools.append(F64_BITS)
        elif p == "f32":
            pools.append(F32_BITS)
        else:
            pools.append(None)  # i32: address or small int, chosen below
    vecs = [[]]
    for i, p in enumerate(params):
        if p == "i32":
            pool = ADDR_V if i == 0 and is_mem else I32_V
        else:
            pool = pools[i]
        vecs = [v + [x] for v in vecs for x in pool]
    # bound the cross product: pairs of 64-bit operands sample the diagonal
    # plus a shifted diagonal, never the full 64-entry square.
    if sum(p in ("f64", "i64") for p in params) >= 2:
        idx64 = [i for i, p in enumerate(params) if p in ("f64", "i64")]
        keep = []
        for v in vecs:
            a, b = (F64_BITS.index(v[idx64[0]]), F64_BITS.index(v[idx64[1]]))
            if b in (a, (a + 3) % len(F64_BITS)):
                keep.append(v)
        vecs = keep
    return vecs


def to_py(ty, bits):
    if ty == "f64":
        return struct.unpack("<d", struct.pack("<Q", bits))[0]
    if ty == "f32":
        return struct.unpack("<f", struct.pack("<I", bits))[0]
    if ty == "i64":
        return bits - (1 << 64) if bits >> 63 else bits
    return bits


def from_py(ty, v):
    if ty == "f64":
        return struct.unpack("<Q", struct.pack("<d", v))[0]
    if ty == "f32":
        return struct.unpack("<I", struct.pack("<f", v))[0]
    if ty == "i64":
        return v & M64
    return v & 0xFFFFFFFF


def is_nan(ty, b):
    if ty == "f64":
        return (b >> 52) & 0x7FF == 0x7FF and b & ((1 << 52) - 1)
    if ty == "f32":
        return (b >> 23) & 0xFF == 0xFF and b & 0x7FFFFF
    return False


def encode_thm_call(site, target):
    off = target - (site + 4)
    assert -(1 << 24) <= off < (1 << 24) and off % 2 == 0
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    j1, j2 = (~(i1 ^ s)) & 1, (~(i2 ^ s)) & 1
    hw1 = 0xF000 | (s << 10) | ((off >> 12) & 0x3FF)
    hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | ((off >> 1) & 0x7FF)
    return struct.pack("<HH", hw1, hw2)


def load(path):
    ef = ELFFile(open(path, "rb"))
    t = ef.get_section_by_name(".text")
    code, base = bytearray(t.data()), t["sh_addr"]
    syms, symtab, membase = {}, None, MEM
    for s in ef.iter_sections():
        if s["sh_type"] == "SHT_SYMTAB":  # #489: symtab, not disasm text
            symtab = s
            for y in s.iter_symbols():
                if y.name and y["st_info"]["type"] == "STT_FUNC":
                    syms[y.name] = y["st_value"] & ~1
                # A self-contained image's startup loads R11 from this symbol,
                # and its OPTIMIZED-path functions address linear memory
                # absolutely through it — the harness must agree.
                if y.name == "__linear_memory_base":
                    membase = y["st_value"]
    stubs = {}
    rel = ef.get_section_by_name(".rel.text")
    if rel is not None:
        for r in rel.iter_relocations():
            sym = symtab.get_symbol(r["r_info_sym"])
            name = sym.name
            if r["r_info_type"] != 10:
                fail(f"{path}: unexpected relocation type to {name!r}")
            if name in AEABI:
                # #1069 single-precision route: an external builtin — bind
                # it to a Python stub (hooked in `emulate`).
                addr = next((a for a, n in stubs.items() if n == name),
                            STUB + 4 * len(stubs))
                stubs[addr] = name
            elif sym["st_shndx"] != "SHN_UNDEF" and name in syms:
                addr = syms[name]
            else:
                fail(f"{path}: unresolvable relocation to {name!r}")
            site = r["r_offset"]
            code[site - base:site - base + 4] = encode_thm_call(site, addr)
    for n in AEABI:
        syms.pop(n, None)
    return bytes(code), base, syms, stubs, membase


def place_args(uc, params, args):
    """AAPCS-VFP: core words R0..R3 (i64 even-aligned), f32 S-slots with
    back-fill, f64 even-aligned D-slots."""
    ncrn, sused = 0, [False] * 16
    for ty, v in zip(params, args):
        if ty in ("i32",):
            assert ncrn < 4
            uc.reg_write(getattr(A, f"UC_ARM_REG_R{ncrn}"), v)
            ncrn += 1
        elif ty == "i64":
            ncrn += ncrn & 1
            assert ncrn <= 2
            uc.reg_write(getattr(A, f"UC_ARM_REG_R{ncrn}"), v & 0xFFFFFFFF)
            uc.reg_write(getattr(A, f"UC_ARM_REG_R{ncrn + 1}"), v >> 32)
            ncrn += 2
        elif ty == "f32":
            k = sused.index(False)
            sused[k] = True
            uc.reg_write(getattr(A, f"UC_ARM_REG_S{k}"), v)
        else:
            k = next(d for d in range(8) if not sused[2 * d] and not sused[2 * d + 1])
            sused[2 * k] = sused[2 * k + 1] = True
            uc.reg_write(getattr(A, f"UC_ARM_REG_D{k}"), v)


def emulate(text, base, entry, params, res, args, garbage, rng, mem, stubs, membase=MEM):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    uc.ctl_set_cpu_model(A.UC_CPU_ARM_MAX)
    lo = base & ~0xFFF
    uc.mem_map(lo, ((base - lo + len(text)) + 0x1FFF) & ~0xFFF)
    uc.mem_write(base, text)
    uc.mem_map(STK, STKSZ)
    uc.mem_map(RET, 0x1000)
    uc.mem_map(MEM, 0x20000)
    uc.mem_write(membase, mem)
    if stubs:
        uc.mem_map(STUB, 0x1000)
        uc.mem_write(STUB, b"\x70\x47" * 0x800)  # bx lr

        def on_stub(uc_, address, _size, _user):
            name = stubs.get(address)
            if name is not None:
                v = AEABI[name](uc_.reg_read(A.UC_ARM_REG_R0) & 0xFFFFFFFF,
                                uc_.reg_read(A.UC_ARM_REG_R1) & 0xFFFFFFFF)
                uc_.reg_write(A.UC_ARM_REG_R0, v & 0xFFFFFFFF)
                uc_.reg_write(A.UC_ARM_REG_R1, v >> 32)
                # AAPCS: the builtin may clobber every caller-saved register.
                for r in (2, 3, 12):
                    uc_.reg_write(getattr(A, f"UC_ARM_REG_R{r}"), 0xDEAD0000 | r)
                for k in range(16):
                    uc_.reg_write(getattr(A, f"UC_ARM_REG_S{k}"), 0x7FC0DEAD)

        uc.hook_add(UC_HOOK_CODE, on_stub, begin=STUB, end=STUB + 0xFFF)
    if garbage:
        uc.mem_write(STK, rng.randbytes(STKSZ))
    uc.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)
    uc.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)
    uc.reg_write(A.UC_ARM_REG_FPSCR, 0)
    for i in range(32):
        uc.reg_write(getattr(A, f"UC_ARM_REG_S{i}"), rng.getrandbits(32) if garbage else 0)
    for i in range(13):
        uc.reg_write(getattr(A, f"UC_ARM_REG_R{i}"), rng.getrandbits(32) if garbage else 0)
    uc.reg_write(A.UC_ARM_REG_R11, membase)
    uc.reg_write(A.UC_ARM_REG_R10, 0x10000)
    uc.reg_write(A.UC_ARM_REG_SP, SP0)
    uc.reg_write(A.UC_ARM_REG_LR, RET | 1)
    place_args(uc, params, args)
    try:
        uc.emu_start(entry | 1, RET, count=200000)
    except UcError as e:
        return ("trap", str(e))
    if uc.reg_read(A.UC_ARM_REG_PC) != RET:
        return ("hang", hex(uc.reg_read(A.UC_ARM_REG_PC)))
    if res == "i32":
        return ("ok", uc.reg_read(A.UC_ARM_REG_R0) & 0xFFFFFFFF)
    if res == "i64":
        return ("ok", (uc.reg_read(A.UC_ARM_REG_R0) & 0xFFFFFFFF)
                | ((uc.reg_read(A.UC_ARM_REG_R1) & 0xFFFFFFFF) << 32))
    if res == "f32":
        return ("ok", uc.reg_read(A.UC_ARM_REG_S0) & 0xFFFFFFFF)
    return ("ok", uc.reg_read(A.UC_ARM_REG_D0) & M64)


def needs_f64(name):
    params, res, body = FUNCS[name]
    return "f64" in params or res == "f64" or "f64" in body


def main():
    wat = module_wat()
    mem = mem_image()
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wasmtime.wat2wasm(wat))
    ref = {}
    for name, (params, res, _body) in FUNCS.items():
        for args in arg_vectors(params, _body):
            st = wasmtime.Store(eng)
            inst = wasmtime.Instance(st, mod, [])
            inst.exports(st)["mem"].write(st, mem, 0)
            got = inst.exports(st)[name](st, *[to_py(t, a) for t, a in zip(params, args)])
            ref[(name, tuple(args))] = from_py(res, got)
    rng = random.Random(0x1603)
    total = bad = 0
    table = {}
    with tempfile.TemporaryDirectory() as tmp:
        wpath = Path(tmp) / "reinterp_1603.wat"
        wpath.write_text(wat)
        for target, reloc in CONFIGS:
            label = f"{target} {'rel' if reloc else 'sc'}"
            out = str(Path(tmp) / f"{target}_{'rel' if reloc else 'sc'}.o")
            cmd = [SYNTH, "compile", str(wpath), "-o", out, "-t", target,
                   "--all-exports", "--allow-skipped-exports"]
            if reloc:
                cmd.append("--relocatable")
            r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if r.returncode != 0:
                fail(f"{label}: compile rc={r.returncode}:\n{r.stdout[-3000:]}")
            skipped = dict(re.findall(r"skipping function '([^']+)': (.*)", r.stdout))
            text, base, syms, stubs, membase = load(out)
            for name, (params, res, _) in FUNCS.items():
                dp_target = target == "cortex-m7dp"
                if name in skipped:
                    why = skipped[name]
                    if not dp_target and needs_f64(name):
                        table[(label, name)] = "declined(sp)"
                        if not re.search(r"double-precision|single-precision|cannot compile", why):
                            fail(f"{label}: '{name}' declined for an unexpected reason: {why}")
                        continue
                    table[(label, name)] = "DECLINED"
                    if name in EXPECTED_DECLINES and EXPECTED_DECLINES[name] in why:
                        table[(label, name)] = f"declined({EXPECTED_DECLINES[name]})"
                        continue
                    print(f"  DECLINE {label} {name}: {why[:200]}")
                    bad += 1
                    continue
                if not dp_target and needs_f64(name):
                    table[(label, name)] = "COMPILED-ON-SP"
                    print(f"  {label}: '{name}' needs f64 but compiled on a "
                          f"single-precision target")
                    bad += 1
                    continue
                unexpected = name in EXPECTED_DECLINES and dp_target
                if unexpected:
                    print(f"  {label}: '{name}' was pinned to decline "
                          f"({EXPECTED_DECLINES[name]}) but compiled — unpin it")
                    bad += 1
                if name not in syms:
                    fail(f"{label}: export '{name}' has no symbol")
                ok = n = 0
                for args in arg_vectors(params, FUNCS[name][2]):
                    want = ref[(name, tuple(args))]
                    for garbage in (False, True):
                        got = emulate(text, base, syms[name], params, res, args,
                                      garbage, rng, mem, stubs, membase)
                        n += 1
                        good = got[0] == "ok" and (
                            got[1] == want or (is_nan(res, got[1]) and is_nan(res, want)))
                        if good:
                            ok += 1
                        elif bad < 16:
                            print(f"  WRONG {label} {name} args={[hex(a) for a in args]} "
                                  f"{'garbage' if garbage else 'zeroed'}: want {want:#x} got "
                                  f"{got if got[0] != 'ok' else hex(got[1])}")
                        bad += 0 if good else 1
                total += n
                table[(label, name)] = ("ok" if ok == n else f"WRONG {n - ok}/{n}") + (
                    " (unpinned)" if unexpected else "")
    labels = [f"{t} {'rel' if r else 'sc'}" for t, r in CONFIGS]
    print(f"{'export':18s} " + " ".join(f"{lb:18s}" for lb in labels))
    for name in FUNCS:
        print(f"{name:18s} " + " ".join(f"{table.get((lb, name), '-'):18s}" for lb in labels))
    print(f"emulations: {total}")
    if MAP:
        print(f"(map mode) {bad} failures")
        return
    if bad:
        fail(f"{bad} failures (wrong values or unexpected declines) over {total} "
             f"emulations — an f64<->i64 bit-cast did not deliver its 64-bit "
             f"pattern where the next consumer reads it (#1603)")
    print(f"PASS: {total} emulations bit-identical to wasmtime (cortex-m7dp rel + "
          f"self-contained, zeroed and garbage machine; cortex-m7 declines f64 loudly)")


if __name__ == "__main__":
    main()
