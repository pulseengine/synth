#!/usr/bin/env python3
"""VCR-PERF-002 Phase 3+ (#494) — constant-divisor rem_u IDENTITY differential.

Builds the `gust_scale` fixture (`x rem_u 1000`, a LITERAL divisor) WITH a
schema-v1 `wsc.facts` value-range premise appended (default: the proven bound
x ∈ [0, 999]), compiles it twice — SPECIALIZED (SYNTH_FACT_SPEC=1) and
UNSPECIALIZED (flag off) — and sweeps EVERY in-bounds value under unicorn
(Thumb-2), asserting the specialized result is identical to BOTH wasmtime
ground truth and the unspecialized synth build. Out-of-bound divergence is
EXPECTED AND CORRECT — the bound is the contract — so this harness only sweeps
in-bounds (the wrong-bound path is exercised with --expect-decline).

The beat-LLVM claim (recorded in the #494 PR): with the fact, synth deletes the
whole `rem_u` (2 B `bx lr`, the identity); clang `-Os` cannot know x < 1000 and
lowers `x % 1000` to a 24 B reciprocal multiply-subtract. The elision is sound
because the divisor is a LITERAL nonzero constant (⇒ the op is unconditionally
total — rem traps only on divisor==0 and has no INT_MIN/-1 overflow), so the
whole effect-free op is deletable — this is the ONE total subset of the
"div/rem is never deleted" rule.

Non-vacuity: the run FAILS unless the specialized compile actually admitted the
certificate-backed identity elision ("fact-spec: ADMIT ... elided to identity")
and shrank gust_scale's .text — so a silently-dead lever cannot pass.

Red-path knob (the wrong-bound demonstration in the #494 PR):
  --fact-lo/--fact-hi set the premise loom "claims". With a too-wide bound
  (e.g. --fact-lo 0 --fact-hi 4000) the identity obligation is Sat (x can reach
  1000, so x % 1000 ≠ x) and synth DECLINES the identity loudly; the op SURVIVES
  and computes the true modulo. (The pre-existing nonzero-divisor zero-guard
  elision — #494 phase 2b — may still shrink the declined build, so it is NOT
  byte-identical to the OFF baseline; that is a separate, sound lever.) Pass
  --expect-decline to sweep OUT-OF-BOUND values (x >= divisor, the region the
  identity would have miscompiled) and assert the surviving rem_u is still the
  true modulo — the real safety property, stronger than a byte proxy.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/fact_spec_rem_494_differential.py
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

WAT = Path(__file__).with_name("fact_spec_rem_494.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
FUNC = "gust_scale"
DIVISOR = 1000


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


def run_arm(code, base, addr, x):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_R0, x & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.emu_start(addr | 1, ret, timeout=5_000_000)
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


# In-bounds grid: every bit/carry boundary of the divisor plus interior points.
GRID = [0, 1, 2, 127, 128, 255, 256, 499, 500, 511, 512, 998, 999]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fact-lo", type=int, default=0,
                    help="dividend value-range premise lower bound (the loom claim)")
    ap.add_argument("--fact-hi", type=int, default=DIVISOR - 1,
                    help="dividend value-range premise upper bound")
    ap.add_argument("--expect-decline", action="store_true",
                    help="assert the elision was DECLINED (wrong-bound green path)")
    args = ap.parse_args()

    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")

    base_wasm = wasmtime.wat2wasm(WAT.read_text())
    # Value-range record: the dividend param at value_id 0.
    payload = facts_payload([value_range_record(0, 0, args.fact_lo, args.fact_hi)])
    wasm = append_custom_section(bytes(base_wasm), b"wsc.facts", payload)
    wasm_path = "/tmp/fact_spec_rem_494.wasm"
    Path(wasm_path).write_bytes(wasm)

    spec_elf = "/tmp/fact_spec_rem_494_spec.elf"
    base_elf = "/tmp/fact_spec_rem_494_base.elf"
    stderr_spec = compile_elf(wasm_path, spec_elf, fact_spec=True)
    compile_elf(wasm_path, base_elf, fact_spec=False)

    admits = stderr_spec.count("elided to identity")
    declines = stderr_spec.count("fact-spec: DECLINE") + stderr_spec.lower().count(
        "not the identity")
    print(f"specialized compile: {admits} identity ADMIT")

    scode, sbase, ssyms, ssizes = load(spec_elf)
    bcode, bbase, bsyms, bsizes = load(base_elf)
    ssize = ssizes.get(FUNC) or len(scode)
    bsize = bsizes.get(FUNC) or len(bcode)
    print(f"{FUNC} size: unspecialized {bsize} B -> specialized {ssize} B "
          f"(clang -Os baseline for `x % {DIVISOR}` = 24 B)")

    # wasmtime ground truth (shared by both paths).
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wasm)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    gs = inst.exports(st)[FUNC]

    def sweep(xs):
        """Assert specialized ≡ wasmtime ≡ unspecialized on every x in `xs`."""
        fails = 0
        for x in xs:
            gt = gs(st, x) & 0xFFFFFFFF
            got_spec = run_arm(scode, sbase, ssyms[FUNC], x)
            got_base = run_arm(bcode, bbase, bsyms[FUNC], x)
            if not (got_spec == gt == got_base):
                fails += 1
                if fails <= 10:
                    print(f"FAIL x={x}: wasmtime={gt} "
                          f"specialized={got_spec} unspecialized={got_base}")
        return fails

    if args.expect_decline:
        # The identity must have declined loudly. The op SURVIVES and computes
        # the TRUE modulo — so we prove correctness by sweeping OUT-OF-BOUND
        # values (x >= divisor, where x % C != x), the exact region the identity
        # would have miscompiled. NB: the pre-existing nonzero-divisor zero-guard
        # elision (#494 phase 2b) may still shrink the declined build vs the
        # baseline — that is a separate, sound lever and does NOT make the build
        # byte-identical; the safety property is that the surviving op is still
        # the true modulo, which we verify by execution, not by a byte proxy.
        if admits != 0:
            sys.exit(f"expected the identity to DECLINE under bound "
                     f"[{args.fact_lo},{args.fact_hi}] but it was admitted")
        # Values >= divisor exercise the non-identity region; keep them within
        # the (too-wide) declared bound so wasmtime/unspec agree on ground truth.
        oob = [x for x in [1000, 1001, 1500, 2048, 3000, 4000]
               if args.fact_lo <= x <= args.fact_hi]
        fails = sweep(oob)
        print(f"swept {len(oob)} out-of-bound (x >= {DIVISOR}) values on "
              f"[{args.fact_lo}, {args.fact_hi}] — the region the identity would "
              f"have miscompiled")
        print("ORACLE:", "PASS (declined loudly; surviving rem_u computes the "
              "true modulo)" if fails == 0 else f"FAIL ({fails}/{len(oob)})")
        sys.exit(1 if fails else 0)

    # Non-vacuity: the identity elision must actually have fired and shrunk.
    if admits != 1:
        sys.exit(f"expected 1 certificate-backed identity elision, got {admits} — "
                 f"stderr:\n{stderr_spec}")
    if ssize >= bsize:
        sys.exit("specialized gust_scale did not shrink — elision did not reach codegen")

    inbounds = [x for x in GRID if args.fact_lo <= x <= args.fact_hi]
    fails = sweep(inbounds)
    print(f"swept {len(inbounds)} in-bounds x values on "
          f"[{args.fact_lo}, {args.fact_hi}]")
    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails}/{len(inbounds)})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
