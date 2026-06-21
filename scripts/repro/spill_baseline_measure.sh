#!/usr/bin/env bash
# VCR-PERF-001 Pass-1 / VCR-RA-010 — in-tree spill-elimination baseline (#390, #242).
#
# gale #390 measured the headline size gap on the gust scheduler hot path
# (gust_poll 816 B / 240 insns vs 208 B / 104 native): "Pass 1 — NO register
# allocation: every wasm local/operand spilled to a stack slot, the `sched`
# pointer reloaded from [sp,#0x3c] 10×. ~288 B (47%). THE HEADLINE."
#
# This script REPRODUCES that mechanism on synth's OWN frozen fixtures, so the
# Pass-1 waste is a regression-tracked number in-tree (not only on gale's
# silicon), and so the eventual spill-eliminating wiring has a measurable target.
# It changes ZERO codegen bytes — it only compiles the frozen fixtures and reads
# the emitted ARM + synth's existing SYNTH_SHADOW_ALLOC instrumentation.
#
# KEY FINDING (2026-06-21, debug binary): the [sp,#] spills are SPURIOUS. synth
# keeps WASM locals frame-resident BY MODEL (local.get -> ldr [sp]; local.set ->
# str [sp]), NOT because of register pressure — the shadow allocator reports peak
# *value*-pressure 7-8 (<= 9), i.e. every live value fits the R0-R8 pool. A
# value-based SSA allocator (VCR-RA-001, currently shadow-only behind
# SYNTH_SHADOW_ALLOC) promotes them into registers and eliminates the spill
# traffic. The default-on range-realloc (v0.11.36) only RENAMES within segments —
# it never adds/removes instructions, so it provably cannot capture Pass-1.
#
# It also DATA-RESOLVES the const-CSE-vs-spill fork: const/remat opportunities are
# 0-2 on these kernels (synth already lowers consts as immediates), while spill
# elimination is 56/39/6 — the spill axis is where the bytes are.
#
# Requires: a built `synth` (target/debug/synth) and an ARM disassembler
# (arm-none-eabi-objdump preferred; llvm-objdump --triple=thumbv7em-none-eabi as
# fallback). Distinguishes [sp,#] spill slots from [fp/r11] linear-memory access.
#
# Run from repo root:
#   scripts/repro/spill_baseline_measure.sh
set -euo pipefail

SYNTH="${SYNTH:-./target/debug/synth}"
FIXTURES=(flight_seam_flat flight_seam control_step)

# Pick a thumb-capable disassembler.
disasm() { # $1 = elf
  if command -v arm-none-eabi-objdump >/dev/null 2>&1; then
    arm-none-eabi-objdump -d -M force-thumb "$1" 2>/dev/null
  elif command -v llvm-objdump >/dev/null 2>&1; then
    llvm-objdump -d --triple=thumbv7em-none-eabi "$1" 2>/dev/null
  else
    echo "ERROR: need arm-none-eabi-objdump or llvm-objdump on PATH" >&2
    exit 2
  fi
}

[ -x "$SYNTH" ] || { echo "ERROR: build synth first (cargo build) — $SYNTH missing" >&2; exit 2; }

printf '%-18s | %5s | %11s | %12s | %s\n' "fixture" "insns" "spill[sp,#]" "linmem[fp]" "shadow-alloc (peak value-pressure / remat)"
printf -- '-------------------|-------|-------------|--------------|-------------------------------------------\n'

for fx in "${FIXTURES[@]}"; do
  wasm="scripts/repro/${fx}.wasm"
  elf="/tmp/${fx}.spillbase.elf"
  [ -f "$wasm" ] || { echo "skip $fx (no $wasm)"; continue; }

  # Compile + capture the shadow allocator's verdict (zero byte change either way).
  shadow=$(SYNTH_SHADOW_ALLOC=1 "$SYNTH" compile "$wasm" -o "$elf" \
            --target cortex-m4 --all-exports --relocatable 2>&1 \
            | grep -iE 'shadow-alloc' | tr '\n' ';' | sed 's/\[shadow-alloc\] //g')

  d=$(disasm "$elf")
  insns=$(echo "$d"  | grep -cE '^\s+[0-9a-f]+:\s' || true)
  spill=$(echo "$d"  | grep -iE '\b(ldr|str)' | grep -iE '\[sp'        | grep -viE 'push|pop' | wc -l | tr -d ' ')
  linmem=$(echo "$d" | grep -iE '\b(ldr|str)' | grep -iE '\[(fp|r11)'                        | wc -l | tr -d ' ')

  printf '%-18s | %5s | %11s | %12s | %s\n' "$fx" "$insns" "$spill" "$linmem" "${shadow:0:60}"
done

cat <<'EOF'

Interpretation:
  spill[sp,#]  = Pass-1 waste (VCR-PERF-001). SPURIOUS when peak value-pressure
                 <= 9 — eliminable by the value-based allocator (VCR-RA-001).
  linmem[fp/r11] = legitimate linear-memory access (r11 = mem base). Not a spill.
  Kill-criterion: wiring the spill-eliminating allocator drops spill[sp,#] toward
  0 on these fixtures with peak value-pressure unchanged — then re-freeze +
  differential + gale on-silicon (the #193/#212/#215 latent-regalloc lesson).
EOF
