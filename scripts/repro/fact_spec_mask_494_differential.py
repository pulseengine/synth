#!/usr/bin/env python3
"""VCR-PERF-002 Phase 3+ (#494) — redundant-mask (narrowing) elision oracle.

Builds the `gust_kernel` lane-pack fixture WITH schema-v1 `wsc.facts`
value-range premises appended (default: both lanes proven ∈ [0, 2047]),
compiles it twice — SPECIALIZED (SYNTH_FACT_SPEC=1) and UNSPECIALIZED (flag
off) — and asserts three things:

  (a) BYTE WIN — the specialized `gust_kernel` .text is strictly smaller: each
      redundant `& 0x7FF` mask (a `movw + and`, NOT uxtb/uxth-foldable) is
      gone. Non-vacuity: the run FAILS unless exactly 2 certificate-backed
      elisions were admitted AND the function shrank.
  (b) EXECUTION MATCHES wasmtime — sweeps a grid of in-bounds (lo, hi) under
      unicorn (Thumb-2) and asserts specialized ≡ wasmtime ground truth ≡
      unspecialized synth. Out-of-bound behavior is deliberately unconstrained
      (the bound is the contract) so the sweep stays in-bounds.
  (c) SOUND DECLINE without the premise — `--expect-decline` re-runs with a
      wrong (too-wide) bound under which `x & 0x7FF != x` is Sat: synth must
      DECLINE loudly (0 admits) and emit a byte-identical-to-baseline stream.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/fact_spec_mask_494_differential.py
Exits nonzero on any mismatch.
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("fact_spec_mask_494.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
FUNC = "gust_kernel"


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


def value_range_record(func_index, value_id, lo, hi):
    body = leb_s64(lo) + leb_s64(hi)
    return (
        b"\x01"                       # kind: value-range
        + leb_u32(func_index)
        + leb_u32(value_id)
        + leb_u32(len(body))
        + body
    )


def facts_payload(records):
    out = b"\x01" + leb_u32(len(records))  # version 1, count
    for r in records:
        out += r
    return out


def append_custom_section(wasm, name, payload):
    content = leb_u32(len(name)) + name + payload
    return wasm + b"\x00" + leb_u32(len(content)) + content


# ---- compile + load ----

def compile_elf(wasm_path, out, fact_spec):
    env = {"PATH": "/usr/bin:/bin"}
    if fact_spec:
        env["SYNTH_FACT_SPEC"] = "1"
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
    syms, sizes = {}, {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
                    sizes[sym.name] = sym["st_size"]
    return data, base, syms, sizes


def run_arm(code, base, addr, lo, hi):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_R0, lo & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, hi & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.emu_start(addr | 1, ret, timeout=5_000_000)
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


# The in-bounds grid: lane boundaries + a few interior points (full 2048^2
# cross product is needless — these exercise every bit boundary of 0x7FF).
GRID = [0, 1, 2, 255, 256, 511, 512, 1023, 1024, 1536, 2046, 2047]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fact-lo", type=int, default=0,
                    help="lane value-range premise lower bound (the loom claim)")
    ap.add_argument("--fact-hi", type=int, default=2047,
                    help="lane value-range premise upper bound")
    ap.add_argument("--expect-decline", action="store_true",
                    help="assert the elision was DECLINED (wrong-bound green path)")
    args = ap.parse_args()

    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")

    base_wasm = wasmtime.wat2wasm(WAT.read_text())
    # Two value-range records: lane lo at value_id 0, lane hi at value_id 3.
    payload = facts_payload([
        value_range_record(0, 0, args.fact_lo, args.fact_hi),
        value_range_record(0, 3, args.fact_lo, args.fact_hi),
    ])
    wasm = append_custom_section(bytes(base_wasm), b"wsc.facts", payload)
    wasm_path = "/tmp/fact_spec_mask_494.wasm"
    Path(wasm_path).write_bytes(wasm)

    spec_elf = "/tmp/fact_spec_mask_494_spec.elf"
    base_elf = "/tmp/fact_spec_mask_494_base.elf"
    stderr_spec = compile_elf(wasm_path, spec_elf, fact_spec=True)
    compile_elf(wasm_path, base_elf, fact_spec=False)

    admits = stderr_spec.count("fact-spec: ADMIT")
    declines = stderr_spec.count("fact-spec: DECLINE")
    print(f"specialized compile: {admits} ADMIT, {declines} DECLINE")

    scode, sbase, ssyms, ssizes = load(spec_elf)
    bcode, bbase, bsyms, bsizes = load(base_elf)
    ssize = ssizes.get(FUNC) or len(scode)
    bsize = bsizes.get(FUNC) or len(bcode)
    print(f"{FUNC} size: unspecialized {bsize} B -> specialized {ssize} B")

    if args.expect_decline:
        if admits != 0:
            sys.exit(f"expected DECLINE under bound [{args.fact_lo},{args.fact_hi}] "
                     f"but {admits} elisions were admitted")
        if scode != bcode:
            sys.exit("declined build must be byte-identical to baseline")
        print("ORACLE: PASS (declined loudly, general lowering emitted)")
        return

    # Non-vacuity: both redundant masks must actually be gone.
    if admits != 2:
        sys.exit(f"expected 2 certificate-backed mask elisions, got {admits} — "
                 f"stderr:\n{stderr_spec}")
    if ssize >= bsize:
        sys.exit("specialized gust_kernel did not shrink — elision did not reach codegen")

    # wasmtime ground truth.
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wasm)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    gk = inst.exports(st)[FUNC]

    fails = 0
    checked = 0
    for lo in GRID:
        for hi in GRID:
            if not (args.fact_lo <= lo <= args.fact_hi):
                continue
            if not (args.fact_lo <= hi <= args.fact_hi):
                continue
            checked += 1
            gt = gk(st, lo, hi) & 0xFFFFFFFF
            got_spec = run_arm(scode, sbase, ssyms[FUNC], lo, hi)
            got_base = run_arm(bcode, bbase, bsyms[FUNC], lo, hi)
            if not (got_spec == gt == got_base):
                fails += 1
                if fails <= 10:
                    print(f"FAIL lo={lo} hi={hi}: wasmtime={gt} "
                          f"specialized={got_spec} unspecialized={got_base}")
    print(f"swept {checked} in-bounds (lo, hi) pairs on [{args.fact_lo}, {args.fact_hi}]")
    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails}/{checked})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
