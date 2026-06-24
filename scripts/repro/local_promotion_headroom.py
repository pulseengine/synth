#!/usr/bin/env python3
"""VCR-RA local-promotion scoping spike (#390, #209, epic #242).

The structural gap to native parity is that synth's instruction selector lowers
every wasm local to a FRAME SLOT (`compute_local_layout` → `LocalGet/Set/Tee` emit
`ldr/str [sp,#off]`), so locals never reach the register allocator. This spike
measures, per function on the frozen fixtures, the COST (sp traffic that local
promotion could remove) and the PRESSURE (distinct slots = how many registers
promotion would demand), to cost-and-de-risk the lever before any codegen change.

FINDING (2026-06-24, on v0.13.0 default codegen):

  function              total  sp-traffic   distinct-slots
  control_step_decide    101    6 ( 5%)        2
  flight_algo            109   25 (22%)        4
  filter_step             52    6 (11%)        3
  controller_step         91    8 ( 8%)        1

Distinct slots are 1–4 per function — far below the allocatable pool (R0–R8 minus
result/scratch ≈ 6–7 usable). So on these fixtures EVERY local fits in a register
with room to spare: promotion needs NO spilling, and the spill path — the
historically bug-prone part of regalloc (#193→#226) — is never exercised. The
built VCR-RA `color_graph` would colour a ≤4-node interference graph at trivial
pressure. Headroom is large (flight_algo 22% of instructions are local memory
traffic, ~all removable); risk is low (no-spill). This makes selector-side local
promotion the right next lever toward parity and more tractable than a general
allocator rewrite.

Reproduce (needs arm-none-eabi-objdump + a built ./target/debug/synth):
  python scripts/repro/local_promotion_headroom.py
"""
import re
import subprocess
import sys

SYNTH = "./target/debug/synth"
FIXTURES = ["control_step", "flight_seam"]
# Allocatable ARM integer pool for locals (R0–R8 minus R0/R1 result + ~1 scratch).
USABLE_POOL = 6


def analyze(elf, fixture):
    objdump = subprocess.run(
        ["arm-none-eabi-objdump", "-d", "-M", "force-thumb", elf],
        capture_output=True, text=True,
    ).stdout
    func = None
    funcs = {}
    for line in objdump.splitlines():
        m = re.match(r"[0-9a-f]+ <(\w+)>:", line)
        if m:
            func = m.group(1)
            funcs[func] = {"str": 0, "ldr": 0, "slots": set(), "total": 0}
        if func is None:
            continue
        mi = re.match(r"\s+[0-9a-f]+:\s+[0-9a-f ]+\t(\w+)\s*(.*)", line)
        if not mi:
            continue
        funcs[func]["total"] += 1
        ms = re.search(r"(str|ldr)(?:\.w)?\s+\w+, \[sp(?:, #(\d+))?\]", line)
        if ms:
            funcs[func][ms.group(1)] += 1
            funcs[func]["slots"].add(int(ms.group(2) or 0))
    rows = []
    for fn, d in funcs.items():
        if d["total"] == 0:
            continue
        sp = d["str"] + d["ldr"]
        rows.append((fixture, fn, d["total"], sp, len(d["slots"])))
    return rows


def main():
    all_rows = []
    for fx in FIXTURES:
        r = subprocess.run(
            [SYNTH, "compile", f"scripts/repro/{fx}.wasm", "-o", f"/tmp/lp_{fx}.elf",
             "--target", "cortex-m4", "--all-exports", "--relocatable"],
            capture_output=True, text=True,
        )
        if r.returncode != 0:
            sys.exit(f"compile failed for {fx}: {r.stderr}")
        all_rows += analyze(f"/tmp/lp_{fx}.elf", fx)

    print(f"{'function':24} {'total':>6} {'sp-traffic':>12} {'slots':>6}  fits-pool")
    overpressure = 0
    for fixture, fn, total, sp, slots in all_rows:
        pct = 100 * sp // total if total else 0
        fits = slots <= USABLE_POOL
        overpressure += 0 if fits else 1
        print(f"{fn:24} {total:6} {sp:6} ({pct:2}%) {slots:6}  {'yes' if fits else 'NO — needs spill'}")

    # The scoping assertion: on the frozen fixtures, promotion fits the pool with
    # no spilling. If this ever flips, local promotion would need the spill path and
    # the risk profile changes — re-scope before building.
    if overpressure:
        sys.exit(f"\nSCOPE CHANGED: {overpressure} function(s) exceed the pool — "
                 "local promotion would need spilling; re-scope the lever.")
    print(f"\nAll functions fit the ≈{USABLE_POOL}-reg pool ⇒ local promotion is NO-SPILL "
          "on the frozen fixtures. Headroom = the sp-traffic column; risk = low.")
    print("SCOPE: PASS")


if __name__ == "__main__":
    main()
