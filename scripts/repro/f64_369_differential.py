#!/usr/bin/env python3
"""#369 (GI-FPU-002 phase 2) — EXECUTION-validate the scalar f64 subset on
cortex-m7dp (double-precision VFP).

Lowered set (everything else f64 stays decode-dropped -> loud-skip):
  * f64.const            — full 64-bit pattern via 2x MOVW/MOVT + VMOV Dd,lo,hi
  * f64.promote_f32      — VCVT.F64.F32 (falcon's 3-function blocker)
  * add/sub/mul/div      — VADD/VSUB/VMUL/VDIV .F64
  * abs/neg/sqrt         — VABS/VNEG/VSQRT .F64
  * eq/ne/lt/le/gt/ge    — VCMP.F64 + VMRS + IT (NaN-audited ordered set; the
                           encoder shipped the SAME #712 flag-clobber bug the
                           f32 compares had — MOVS after VMRS — fixed here)
  * f64.load/f64.store   — two PROVEN bounds-checked 4-byte integer accesses
  * f64 live ACROSS an integer call — D0..D7 are caller-saved, preserved as
                           aliased S-word pairs by the #719 VFP call-spill

Each op is differentiated under unicorn vs wasmtime, BIT-EXACT on the 64-bit
result pattern with NaN==NaN per WASM Core §4.3.3 (NaN sign/payload is
non-deterministic; mirrors f32_bits_eq in f32_vfp_619_differential.py).

Honest rejections pinned: the whole fixture on cortex-m4f (single-precision)
and cortex-m3 (no FPU); f64-param functions and f64-returning CALLS on m7dp
(absent from the symtab — loud decline, never a miscompile).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python scripts/repro/f64_369_differential.py
"""
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_D1,
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R11,
    UC_ARM_REG_S0,
    UC_ARM_REG_S1,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("f64_369.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
MEMBASE = 0x20000000  # R11/fp linear-memory base at reset (cortex_m.rs)


def compile_elf(out, target):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", target, "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    return r.returncode == 0, (r.stderr + r.stdout)


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def bits_f64(b):
    return struct.unpack("<d", struct.pack("<Q", b & 0xFFFFFFFFFFFFFFFF))[0]


def bits_f32(b):
    return struct.unpack("<f", struct.pack("<I", b & 0xFFFFFFFF))[0]


def is_nan64(bits):
    b = bits & 0xFFFFFFFFFFFFFFFF
    return (b & 0x7FF0000000000000) == 0x7FF0000000000000 and (
        b & 0x000FFFFFFFFFFFFF) != 0


def f64_bits_eq(got, want):
    """NaN==NaN regardless of sign/payload (WASM Core §4.3.3 leaves NaN
    results non-deterministic); every non-NaN result stays bit-exact."""
    if is_nan64(got) and is_nan64(want):
        return True
    return (got & 0xFFFFFFFFFFFFFFFF) == (want & 0xFFFFFFFFFFFFFFFF)


def new_uc(text, text_base):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    map_base = text_base & ~0xFFF
    size = ((len(text) + (text_base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(text_base, text)
    uc.mem_map(0x30000, 0x10000)  # stack
    uc.mem_map(MEMBASE, 0x10000)  # linear-memory window (R11/fp base)
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    uc.reg_write(UC_ARM_REG_R11, MEMBASE)
    # Enable the FPU (off at reset): CPACR CP10/CP11 + FPEXC.EN.
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    return uc


def run(text, base, addr, mem0=None, mem8=None, r0=None, r1=None, r2=None,
        d0=None, d1=None, s0=None, s1=None):
    uc = new_uc(text, base)
    if mem0 is not None:
        uc.mem_write(MEMBASE + 0, struct.pack("<Q", mem0))
    if mem8 is not None:
        uc.mem_write(MEMBASE + 8, struct.pack("<Q", mem8))
    if r0 is not None:
        uc.reg_write(UC_ARM_REG_R0, r0 & 0xFFFFFFFF)
    if r1 is not None:
        uc.reg_write(UC_ARM_REG_R1, r1 & 0xFFFFFFFF)
    if r2 is not None:
        uc.reg_write(UC_ARM_REG_R2, r2 & 0xFFFFFFFF)
    if d0 is not None:
        uc.reg_write(UC_ARM_REG_D0, d0 & 0xFFFFFFFFFFFFFFFF)
    if d1 is not None:
        uc.reg_write(UC_ARM_REG_D1, d1 & 0xFFFFFFFFFFFFFFFF)
    if s0 is not None:
        uc.reg_write(UC_ARM_REG_S0, s0 & 0xFFFFFFFF)
    if s1 is not None:
        uc.reg_write(UC_ARM_REG_S1, s1 & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=400)
    return uc


def wasm_instance():
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    return store, inst


# 64-bit operand pairs (mem[0], mem[8]) hitting the arithmetic edges.
D = f64_bits
PAIRS = [
    (D(1.5), D(2.25)),
    (D(-0.0), D(0.0)),
    (D(float("inf")), D(-float("inf"))),
    (0x7FF8000000000000, D(1.0)),          # NaN op x
    (D(3.141592653589793), 0x0000000000000001),  # pi op +subnormal-min
    (D(1.7976931348623157e308), D(1.7976931348623157e308)),  # MAX (overflow)
    (D(1.0), D(0.0)),                       # div-by-zero -> inf
    (D(-2.5), D(-2.5)),
]

# f32 bit patterns for promote (covers sign/inf/NaN/subnormal).
PROMOTE_BITS = [
    0x00000000, 0x80000000, 0x3FC00000, 0xBFC00000,
    0x7F800000, 0xFF800000, 0x7FC00000, 0x00000001, 0x7F7FFFFF,
]

RESULT_ADDR = 64  # where the store-result functions write


def main():
    elf = "/tmp/f64_369.elf"

    # Honest-reject: single-precision m4f and no-FPU m3 must SKIP every f64
    # function (the integer helper $fhelp may still compile, so check the
    # symtab rather than the exit code).
    for tgt in ("cortex-m4f", "cortex-m3"):
        out = f"/tmp/f64_369_{tgt}.elf"
        ok, _ = compile_elf(out, tgt)
        if ok:
            _, _, syms = load(out)
            leaked = [s for s in
                      ("dconst", "dadd", "dlt", "dpromote", "dxcall",
                       "dretcall", "dparam", "dparam_mix", "dcallargs",
                       "dcallswap", "dcallmix")
                      if s in syms]
            if leaked:
                sys.exit(f"FAIL: f64 functions {leaked} must be REJECTED on "
                         f"{tgt} (no double-precision FPU)")
        print(f"[{tgt}] f64 functions honest-rejected OK")

    ok, log = compile_elf(elf, "cortex-m7dp")
    if not ok:
        print("RED: `synth compile -t cortex-m7dp` REJECTED the f64 fixture.")
        print(log.strip()[:900])
        sys.exit(1)

    text, base, syms = load(elf)
    store, inst = wasm_instance()
    exp = inst.exports(store)
    mem = exp["mem"]
    fails = 0
    checked = 0

    def fail(msg):
        nonlocal fails
        fails += 1
        print("  MISMATCH " + msg)

    def need(name):
        if name not in syms:
            fail(f"symbol '{name}' MISSING — function was skipped, not lowered")
            return False
        return True

    def wasm_store_result(fn, *args):
        """Run the wasmtime twin (which f64.stores at RESULT_ADDR), read back."""
        exp[fn](store, *args)
        return struct.unpack("<Q", bytes(
            mem.read(store, RESULT_ADDR, RESULT_ADDR + 8)))[0]

    def set_wasm_mem(a, b):
        mem.write(store, struct.pack("<Q", a), 0)
        mem.write(store, struct.pack("<Q", b), 8)

    # ---- f64.const ----------------------------------------------------------
    for fn in ("dconst", "dconst_pi", "dconst_nz"):
        if not need(fn):
            continue
        uc = run(text, base, syms[fn], r0=RESULT_ADDR)
        got = struct.unpack("<Q", bytes(uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
        want = wasm_store_result(fn, RESULT_ADDR)
        checked += 1
        if got != want:
            fail(f"{fn} -> 0x{got:016x} != wasmtime 0x{want:016x}")
        else:
            print(f"[{fn}] 0x{got:016x} (bit-exact) OK")

    # ---- f64.promote_f32 ----------------------------------------------------
    if need("dpromote"):
        for b32 in PROMOTE_BITS:
            uc = run(text, base, syms["dpromote"], r0=RESULT_ADDR, r1=b32)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            want = wasm_store_result("dpromote", RESULT_ADDR, b32)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"dpromote(0x{b32:08x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
            else:
                print(f"[dpromote] 0x{b32:08x} -> 0x{got:016x} OK")

    # ---- binary + unary arithmetic ------------------------------------------
    for fn in ("dadd", "dsub", "dmul", "ddiv", "dabs", "dneg", "dsqrt"):
        if not need(fn):
            continue
        for a, b in PAIRS:
            uc = run(text, base, syms[fn], mem0=a, mem8=b, r0=RESULT_ADDR)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            set_wasm_mem(a, b)
            want = wasm_store_result(fn, RESULT_ADDR)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"{fn}(0x{a:016x}, 0x{b:016x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
        print(f"[{fn}] {len(PAIRS)} edge pairs OK")

    # ---- the six comparisons (NaN rows: every ordered relation false, ne true)
    for fn in ("deq", "dne", "dlt", "dle", "dgt", "dge"):
        if not need(fn):
            continue
        for a, b in PAIRS:
            uc = run(text, base, syms[fn], mem0=a, mem8=b)
            got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            set_wasm_mem(a, b)
            want = exp[fn](store) & 0xFFFFFFFF
            checked += 1
            if got != want:
                fail(f"{fn}(0x{a:016x}, 0x{b:016x}) -> {got} "
                     f"!= wasmtime {want}")
        print(f"[{fn}] {len(PAIRS)} edge pairs OK")

    # ---- f64 live ACROSS an integer call (D-file caller-saved spill) --------
    if need("dxcall"):
        for (a, _), b32 in zip(PAIRS, PROMOTE_BITS):
            uc = run(text, base, syms["dxcall"], mem0=a, r0=RESULT_ADDR, r1=b32)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            set_wasm_mem(a, 0)
            want = wasm_store_result("dxcall", RESULT_ADDR, b32)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"dxcall(0x{a:016x}, 0x{b32:08x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
            else:
                print(f"[dxcall] (0x{a:016x},0x{b32:08x}) -> 0x{got:016x} OK "
                      f"(f64 live across bl)")

    # ---- GI-FPU-002 phase 3 (#369): f64 RESULT marshalled out of D0 ---------
    # dretcall(addr): mem[addr] = mem[0] + dret() where dret() = mem[8] + 2.5
    # computes in D0 — a caller reading R0:R1, or failing to preserve its live
    # double around the bl, diverges at the value level.
    if need("dretcall"):
        for a, b in PAIRS:
            uc = run(text, base, syms["dretcall"], mem0=a, mem8=b,
                     r0=RESULT_ADDR)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            set_wasm_mem(a, b)
            want = wasm_store_result("dretcall", RESULT_ADDR)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"dretcall(0x{a:016x}, 0x{b:016x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
            else:
                print(f"[dretcall] (0x{a:016x},0x{b:016x}) -> 0x{got:016x} OK "
                      f"(D0 result marshalled)")

    # ---- GI-FPU-002 phase 3 (#369): f64 PARAMS homed in D-registers ---------
    # dparam(f64 x, i32 addr): mem[addr] = x. x in D0, addr in R0 (core walk
    # skips the D-homed f64); R0:R1 poisoned-by-addr, R1 poisoned explicitly.
    if need("dparam"):
        for a, _ in PAIRS:
            uc = run(text, base, syms["dparam"], d0=a, r0=RESULT_ADDR,
                     r1=0xBADC0DE)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            want = wasm_store_result("dparam", bits_f64(a), RESULT_ADDR)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"dparam(0x{a:016x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
            else:
                print(f"[dparam] 0x{a:016x} -> stored bit-exact OK (D0 home)")

    # dparam_mix(f32 a, f64 b, f32 c, i32 addr): back-fill homes S0, D1, S1 —
    # c read from the back-filled S1 (a sequential-S misassignment diverges).
    if need("dparam_mix"):
        for ab, b64, cb in ((0x3FC00000, D(2.25), 0x40200000),
                            (0x80000000, D(-0.0), 0x00000000),
                            (0xC2F60000, D(1e10), 0x00000001),
                            (0x7F800000, D(-1.5), 0x3F800000)):
            uc = run(text, base, syms["dparam_mix"], s0=ab, s1=cb, d1=b64,
                     r0=RESULT_ADDR, r1=0xBADC0DE)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            want = wasm_store_result("dparam_mix", bits_f32(ab),
                                     bits_f64(b64), bits_f32(cb), RESULT_ADDR)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"dparam_mix(0x{ab:08x},0x{b64:016x},0x{cb:08x}) -> "
                     f"0x{got:016x} != wasmtime 0x{want:016x}")
            else:
                print(f"[dparam_mix] -> 0x{got:016x} OK (S0/D1/S1 back-fill)")

    # dparam_home(f64 x, i32 b, i32 addr): the D0 param home must survive an
    # integer call whose callee clobbers S0/S1 (=D0).
    if need("dparam_home"):
        for (a, _), b32 in zip(PAIRS, PROMOTE_BITS):
            uc = run(text, base, syms["dparam_home"], d0=a, r0=b32,
                     r1=RESULT_ADDR)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            want = wasm_store_result("dparam_home", bits_f64(a), b32,
                                     RESULT_ADDR)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"dparam_home(0x{a:016x},0x{b32:08x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
            else:
                print(f"[dparam_home] (0x{a:016x},0x{b32:08x}) -> "
                      f"0x{got:016x} OK (D0 home across bl)")

    # ---- GI-FPU-002 phase 3 (#369): f64 ARGS marshalled into D0/D1 ----------
    # dcallargs: in-place sources; dcallswap: CROSS-SWAPPED sources through the
    # two-phase staging (D0 local home <-> D1 temp); dcallmix: int+f64 mixed.
    for fn in ("dcallargs", "dcallswap"):
        if not need(fn):
            continue
        for a, b in PAIRS:
            uc = run(text, base, syms[fn], mem0=a, mem8=b, r0=RESULT_ADDR)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            set_wasm_mem(a, b)
            want = wasm_store_result(fn, RESULT_ADDR)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"{fn}(0x{a:016x}, 0x{b:016x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
        print(f"[{fn}] {len(PAIRS)} edge pairs OK (D-file args marshalled)")
    if need("dcallmix"):
        for (a, _), b32 in zip(PAIRS, PROMOTE_BITS):
            uc = run(text, base, syms["dcallmix"], mem0=a, r0=RESULT_ADDR,
                     r1=b32)
            got = struct.unpack("<Q", bytes(
                uc.mem_read(MEMBASE + RESULT_ADDR, 8)))[0]
            set_wasm_mem(a, 0)
            want = wasm_store_result("dcallmix", RESULT_ADDR, b32)
            checked += 1
            if not f64_bits_eq(got, want):
                fail(f"dcallmix(0x{a:016x},0x{b32:08x}) -> 0x{got:016x} "
                     f"!= wasmtime 0x{want:016x}")
            else:
                print(f"[dcallmix] (0x{a:016x},0x{b32:08x}) -> 0x{got:016x} "
                      f"OK (mixed int+f64 args)")

    if fails:
        sys.exit(f"\nFAIL: {fails}/{checked} f64 #369 results diverged")
    print(f"\nGREEN: {checked}/{checked} f64 #369 results bit-exact vs wasmtime "
          f"(const/promote/arith/compare/load/store + f64-across-call + "
          f"phase-3 f64 param D-homes (incl. back-fill + across-call) + "
          f"D0/D1 argument + D0 result call marshalling on cortex-m7dp; "
          f"m4f + m3 honest-reject confirmed).")


if __name__ == "__main__":
    main()
