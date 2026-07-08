#!/usr/bin/env python3
"""VCR-PERF-002 Phase 2b (#494) — in-bounds differential for the
divisor-nonzero trap-guard elision (oracle 3), plus the red force-admit
divergence demonstration (oracle 4).

Builds scripts/repro/fact_spec_div_494.wat WITH a schema-v1 `wsc.facts`
section appended (green default: d ∈ [1, 64] on the i32 divisors, kind-3
divisor-nonzero on the i64 divisor), compiles it twice — SPECIALIZED
(SYNTH_FACT_SPEC=1) and UNSPECIALIZED — and sweeps the proven bound under
unicorn (Thumb-2), asserting the specialized result is identical to BOTH
wasmtime ground truth and the unspecialized synth build. Out-of-bound
behavior is deliberately unconstrained (the bound is the contract); this
harness only sweeps in-bounds.

Two-guard distinction check (the #633/#634 synergy, oracle 5 at execution
level): qs64 carries ONLY a divisor-nonzero fact, so its INT64_MIN/-1
OVERFLOW guard is retained — this harness asserts qs64(INT64_MIN, -1) TRAPS
in both wasmtime and the SPECIALIZED build (the retained guard fires), while
sweeping nonzero divisors (including negative ones) for value agreement.

Non-vacuity: the run FAILS unless the specialized compile admitted exactly 5
certificate-backed elisions (qu 1, qs 2, ru 1, qs64 1) on stderr.

Modes:
  (default)         green run: in-bounds sweep + the retained-guard trap check.
  --expect-decline  facts claim d ∈ [0, 64] (includes 0): assert the Sat
                    obligation DECLINED loudly and the build is byte-identical
                    to baseline (the guard is restored by the obligation).
  --force-admit     RED run (debug synth builds only): same wrong bound, but
                    SYNTH_FACT_SPEC_FORCE_ADMIT=1 forces the Sat admit —
                    assert qu(1, 0) TRAPS in wasmtime but does NOT trap in the
                    forced build (the divergence an unsound admit would cause,
                    which the in-bounds sweep + certificate gate exist to
                    prevent).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/fact_spec_div_494_differential.py
Exits nonzero on any mismatch.
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("fact_spec_div_494.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
TRAP = "<trap>"


# ---- schema-v1 wsc.facts encoding (docs/design/wsc-facts-encoding.md) ----

def leb_u32(v):
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        out.append(b | (0x80 if v else 0))
        if not v:
            return bytes(out)


def leb_s64(v):
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        done = (v == 0 and not (b & 0x40)) or (v == -1 and (b & 0x40))
        out.append(b | (0 if done else 0x80))
        if done:
            return bytes(out)


def range_fact(func_index, value_id, lo, hi):
    body = leb_s64(lo) + leb_s64(hi)
    return (b"\x01" + leb_u32(func_index) + leb_u32(value_id)
            + leb_u32(len(body)) + body)


def nonzero_fact(func_index, value_id):
    return b"\x03" + leb_u32(func_index) + leb_u32(value_id) + leb_u32(0)


def facts_payload(records):
    return b"\x01" + leb_u32(len(records)) + b"".join(records)


def append_custom_section(wasm, name, payload):
    content = leb_u32(len(name)) + name + payload
    return wasm + b"\x00" + leb_u32(len(content)) + content


# ---- compile + load ----

def compile_elf(wasm_path, out, fact_spec, force_admit=False):
    env = {"PATH": "/usr/bin:/bin"}
    if fact_spec:
        env["SYNTH_FACT_SPEC"] = "1"
    if force_admit:
        env["SYNTH_FACT_SPEC_FORCE_ADMIT"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", str(wasm_path), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed ({out}): {r.stderr}")
    return r.stderr


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] & ~1
    return data, base, syms


def run_arm(code, base, addr, regs):
    """Execute at addr with r0..r3 = regs; return (r0, r1) or TRAP."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2,
                         UC_ARM_REG_R3), regs):
        mu.reg_write(reg, val & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        mu.emu_start(addr | 1, ret, timeout=5_000_000)
    except UcError:
        return TRAP  # UDF (or other fault) = trap
    return (mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF,
            mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF)


def call_wasmtime(store, func, args):
    try:
        return func(store, *args)
    except Exception:
        return TRAP


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--expect-decline", action="store_true",
                    help="claim d ∈ [0,64]: assert Sat loud-decline + byte-identity")
    ap.add_argument("--force-admit", action="store_true",
                    help="RED: wrong bound + SYNTH_FACT_SPEC_FORCE_ADMIT — "
                         "demonstrate the divisor=0 divergence")
    args = ap.parse_args()

    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")

    base_wasm = bytes(wasmtime.wat2wasm(WAT.read_text()))
    tmp = Path("/tmp")

    # ---------- red / decline legs: the claim includes 0 ----------
    if args.expect_decline or args.force_admit:
        wasm = append_custom_section(
            base_wasm, b"wsc.facts",
            facts_payload([range_fact(0, 1, 0, 64)]))
        wasm_path = tmp / "fact_spec_div_494_wrong.wasm"
        wasm_path.write_bytes(wasm)
        spec_elf = str(tmp / "fact_spec_div_494_wrong_spec.elf")
        base_elf = str(tmp / "fact_spec_div_494_wrong_base.elf")
        stderr = compile_elf(wasm_path, spec_elf, fact_spec=True,
                             force_admit=args.force_admit)
        compile_elf(wasm_path, base_elf, fact_spec=False)
        scode, sbase, ssyms = load(spec_elf)
        bcode, _, _ = load(base_elf)

        if args.expect_decline:
            if "fact-spec: ADMIT" in stderr:
                sys.exit(f"expected DECLINE under d ∈ [0,64], got an admit:\n{stderr}")
            if "zero-guard obligation Sat" not in stderr:
                sys.exit(f"decline must name the Sat obligation:\n{stderr}")
            if scode != bcode:
                sys.exit("declined build must be byte-identical to baseline")
            print("ORACLE: PASS (Sat obligation declined loudly; guard restored "
                  "byte-identically)")
            return

        # --force-admit: the unsound build must DIVERGE at divisor == 0.
        if "UNSOUND FORCED ADMIT" not in stderr:
            sys.exit("force-admit run must scream UNSOUND FORCED ADMIT "
                     "(release synth builds compile the lever out):\n" + stderr)
        eng = wasmtime.Engine()
        st = wasmtime.Store(eng)
        inst = wasmtime.Instance(st, wasmtime.Module(eng, wasm), [])
        qu = inst.exports(st)["qu"]
        gt = call_wasmtime(st, qu, (7, 0))
        got = run_arm(scode, sbase, ssyms["qu"], (7, 0))
        print(f"qu(7, 0): wasmtime={gt} forced-specialized={got}")
        if gt != TRAP:
            sys.exit("wasmtime must trap on divide-by-zero")
        if got == TRAP:
            sys.exit("forced build still trapped — the red lever did not elide "
                     "the guard (vacuous red run)")
        print("ORACLE: PASS (red) — the forced admit DIVERGES exactly as the "
              "certificate gate predicts: wasmtime traps, the unsound build "
              "returns a value. This is the wrong-code class the per-site "
              "obligation + this harness exist to prevent.")
        return

    # ---------- green leg: proven facts ----------
    wasm = append_custom_section(
        base_wasm, b"wsc.facts",
        facts_payload([
            range_fact(0, 1, 1, 64),
            range_fact(1, 1, 1, 64),
            range_fact(2, 1, 1, 64),
            nonzero_fact(3, 1),
        ]))
    wasm_path = tmp / "fact_spec_div_494.wasm"
    wasm_path.write_bytes(wasm)
    spec_elf = str(tmp / "fact_spec_div_494_spec.elf")
    base_elf = str(tmp / "fact_spec_div_494_base.elf")
    stderr_spec = compile_elf(wasm_path, spec_elf, fact_spec=True)
    compile_elf(wasm_path, base_elf, fact_spec=False)

    admits = stderr_spec.count("fact-spec: ADMIT")
    declines = stderr_spec.count("fact-spec: DECLINE")
    print(f"specialized compile: {admits} ADMIT, {declines} DECLINE")
    # Non-vacuity: qu 1 (zero), qs 2 (zero + overflow, independent
    # obligations), ru 1 (zero), qs64 1 (zero only — overflow RETAINED).
    if admits != 5:
        sys.exit(f"expected 5 certificate-backed guard elisions, got {admits}:\n"
                 f"{stderr_spec}")
    if "RETAINED" not in stderr_spec:
        sys.exit("the retained i64 overflow guard must decline loudly:\n"
                 + stderr_spec)

    scode, sbase, ssyms = load(spec_elf)
    bcode, bbase, bsyms = load(base_elf)

    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, wasm), [])
    ex = inst.exports(st)

    fails = 0

    def check(tag, gt, got_spec, got_base):
        nonlocal fails
        if not (got_spec == gt == got_base):
            fails += 1
            if fails <= 10:
                print(f"FAIL {tag}: wasmtime={gt} specialized={got_spec} "
                      f"unspecialized={got_base}")

    # i32 sweep over the proven bound d ∈ [1, 64].
    ns = [0, 1, 7, 12345, 2**31 - 1, -8 & 0xFFFFFFFF]
    count = 0
    for fn in ("qu", "qs", "ru"):
        f = ex[fn]
        for n in ns:
            n_signed = n - 2**32 if n >= 2**31 else n
            for d in range(1, 65):
                gt = call_wasmtime(st, f, (n_signed, d))
                gt = gt & 0xFFFFFFFF if gt != TRAP else gt
                got_s = run_arm(scode, sbase, ssyms[fn], (n, d))
                got_s = got_s[0] if got_s != TRAP else got_s
                got_b = run_arm(bcode, bbase, bsyms[fn], (n, d))
                got_b = got_b[0] if got_b != TRAP else got_b
                check(f"{fn}({n_signed}, {d})", gt, got_s, got_b)
                count += 1

    # i64 sweep: the kind-3 claim is d ≠ 0 — nonzero divisors on both sides
    # of zero (the negative ones exercise the sign-handling around the
    # retained overflow guard).
    f64 = ex["qs64"]
    n64s = [0, 1, 9_000_000_000, 2**63 - 1, -5, -(2**63)]
    d64s = [d for d in range(-8, 65) if d != 0]
    for n in n64s:
        for d in d64s:
            if n == -(2**63) and d == -1:
                continue  # the trap case is asserted separately below
            gt = call_wasmtime(st, f64, (n, d))
            nu, du = n & (2**64 - 1), d & (2**64 - 1)
            got_s = run_arm(scode, sbase, ssyms["qs64"],
                            (nu & 0xFFFFFFFF, nu >> 32, du & 0xFFFFFFFF, du >> 32))
            got_b = run_arm(bcode, bbase, bsyms["qs64"],
                            (nu & 0xFFFFFFFF, nu >> 32, du & 0xFFFFFFFF, du >> 32))
            gtv = gt & (2**64 - 1) if gt != TRAP else gt
            gsv = got_s[0] | (got_s[1] << 32) if got_s != TRAP else got_s
            gbv = got_b[0] | (got_b[1] << 32) if got_b != TRAP else got_b
            check(f"qs64({n}, {d})", gtv, gsv, gbv)
            count += 1

    # TWO-GUARD DISTINCTION at execution level (oracle 5): the divisor-nonzero
    # fact elided qs64's zero guard, but INT64_MIN / -1 must STILL trap — the
    # retained #633 overflow guard fires in the SPECIALIZED build too.
    n, d = -(2**63), -1
    gt = call_wasmtime(st, f64, (n, d))
    nu, du = n & (2**64 - 1), d & (2**64 - 1)
    got_s = run_arm(scode, sbase, ssyms["qs64"],
                    (nu & 0xFFFFFFFF, nu >> 32, du & 0xFFFFFFFF, du >> 32))
    print(f"qs64(INT64_MIN, -1): wasmtime={gt} specialized={got_s}")
    if gt != TRAP or got_s != TRAP:
        sys.exit("qs64(INT64_MIN, -1) must trap in BOTH wasmtime and the "
                 "specialized build — the retained overflow guard is the "
                 "two-guard distinction (#633/#634)")
    count += 1

    print(f"swept {count} in-bounds cases")
    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails}/{count})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
