#!/usr/bin/env python3
"""VCR-PERF-002 Phase 2 (#494) — in-bounds differential for the fact-spec
clamp elision (oracle 2 of the design doc's three).

Builds the gust_mix clamp fixture WITH a schema-v1 `wsc.facts` value-range
premise appended (default: the proven bound ch ∈ [524, 1524]), compiles it
twice — SPECIALIZED (SYNTH_FACT_SPEC=1) and UNSPECIALIZED (flag off) — and
sweeps EVERY value of the premise bound under unicorn (Thumb-2), asserting the
specialized result is identical to BOTH wasmtime ground truth and the
unspecialized synth build. Out-of-bound divergence is EXPECTED AND CORRECT —
the bound is the contract (mirrors gale's gust_floor_bench soundness gate
mix_proven ≡ mix_native ≡ gust_mix on [524,1524]); this harness therefore
only sweeps in-bounds.

Non-vacuity: the run FAILS unless the specialized compile actually admitted
2 certificate-backed elisions ("fact-spec: ADMIT" on stderr) and shrank
gust_mix's .text — so a silently-dead lever cannot pass.

Red-path knob (the wrong-bound demonstration in the #494 Phase-2 PR):
  --fact-lo/--fact-hi set the premise loom "claims"; the sweep covers that
  claimed bound. With a deliberately-wrong bound (e.g. --fact-lo 0 --fact-hi
  4000) the obligation is Sat and synth DECLINES (this harness then reports
  the decline and exits 0 with elisions=0 only if --expect-decline is given).
  Forcing an admit under a wrong bound (temporarily bypassing the solver)
  makes this harness FAIL on the in-bounds sweep — that red run is documented
  in the PR body.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/fact_spec_clamp_494_differential.py
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
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_SP

WAT = Path(__file__).with_name("fact_spec_clamp_494.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
FUNC = "gust_mix"


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


def facts_payload(func_index, value_id, lo, hi):
    body = leb_s64(lo) + leb_s64(hi)
    return (
        b"\x01"                      # version 1
        + leb_u32(1)                 # count
        + b"\x01"                    # kind: value-range
        + leb_u32(func_index)
        + leb_u32(value_id)
        + leb_u32(len(body))
        + body
    )


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
    syms = {}
    sizes = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
                    sizes[sym.name] = sym["st_size"]
    return data, base, syms, sizes


def run_arm(code, base, addr, arg):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.emu_start(addr | 1, ret, timeout=5_000_000)
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fact-lo", type=int, default=524,
                    help="value-range premise lower bound (the loom claim)")
    ap.add_argument("--fact-hi", type=int, default=1524,
                    help="value-range premise upper bound")
    ap.add_argument("--expect-decline", action="store_true",
                    help="assert the elision was DECLINED (wrong-bound green path)")
    args = ap.parse_args()

    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")

    # Build the facts-carrying module: fixture wasm + value-range on
    # (func 0, value_id 0 = the local.get producing ch).
    base_wasm = wasmtime.wat2wasm(WAT.read_text())
    wasm = append_custom_section(
        bytes(base_wasm), b"wsc.facts",
        facts_payload(0, 0, args.fact_lo, args.fact_hi))
    wasm_path = "/tmp/fact_spec_clamp_494.wasm"
    Path(wasm_path).write_bytes(wasm)

    spec_elf, base_elf = "/tmp/fact_spec_494_spec.elf", "/tmp/fact_spec_494_base.elf"
    stderr_spec = compile_elf(wasm_path, spec_elf, fact_spec=True)
    compile_elf(wasm_path, base_elf, fact_spec=False)

    admits = stderr_spec.count("fact-spec: ADMIT")
    declines = stderr_spec.count("fact-spec: DECLINE")
    print(f"specialized compile: {admits} ADMIT, {declines} DECLINE")

    scode, sbase, ssyms, ssizes = load(spec_elf)
    bcode, bbase, bsyms, bsizes = load(base_elf)
    # Prefer symtab st_size; fall back to whole-.text length (single-function
    # module) when the builder leaves st_size at 0.
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

    # Non-vacuity: both clamp branches must actually be gone.
    if admits != 2:
        sys.exit(f"expected 2 certificate-backed elisions, got {admits} — "
                 f"stderr:\n{stderr_spec}")
    if ssize >= bsize:
        sys.exit("specialized gust_mix did not shrink — elision did not reach codegen")

    # wasmtime ground truth.
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wasm)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    gm = inst.exports(st)[FUNC]

    # In-bounds sweep — the proven bound, and ONLY the proven bound (the
    # out-of-bound behavior of the specialized build is deliberately
    # unconstrained: the bound is the contract).
    fails = 0
    for ch in range(args.fact_lo, args.fact_hi + 1):
        gt = gm(st, ch) & 0xFFFFFFFF
        got_spec = run_arm(scode, sbase, ssyms[FUNC], ch)
        got_base = run_arm(bcode, bbase, bsyms[FUNC], ch)
        if not (got_spec == gt == got_base):
            fails += 1
            if fails <= 10:
                print(f"FAIL ch={ch}: wasmtime={gt} specialized={got_spec} "
                      f"unspecialized={got_base}")
    n = args.fact_hi - args.fact_lo + 1
    print(f"swept {n} in-bounds values on [{args.fact_lo}, {args.fact_hi}]")
    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails}/{n})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
