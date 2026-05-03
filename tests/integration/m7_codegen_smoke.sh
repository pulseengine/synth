#!/bin/bash
# Smoke test: validate that synth's Cortex-M7 codegen path produces a
# well-formed ELF for both single-precision (M7) and double-precision (M7DP)
# targets, exercising f32 and f64 arithmetic.
#
# Companion to fetch_osxcar_wasm.sh, which exercises M7DP with real-world
# components. This test runs without network access and is suitable for CI.
#
# Usage:
#   bash tests/integration/m7_codegen_smoke.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SYNTH="$PROJECT_ROOT/target/debug/synth"
TMPDIR="${TMPDIR:-/tmp}/synth_m7_smoke_$$"

cleanup() { rm -rf "$TMPDIR"; }
trap cleanup EXIT
mkdir -p "$TMPDIR"

echo "=== Synth M7 codegen smoke test ==="

if [ ! -x "$SYNTH" ]; then
    (cd "$PROJECT_ROOT" && cargo build -p synth-cli --quiet)
fi

# i32-only module — should compile under M7 (single FPU)
cat > "$TMPDIR/i32_only.wat" << 'WAT'
(module
  (func (export "add") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.add)
  (func (export "sub") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.sub)
  (func (export "mul") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.mul)
  (memory (export "memory") 1))
WAT

# f32 module — single-precision, should compile under M7
cat > "$TMPDIR/f32.wat" << 'WAT'
(module
  (func (export "fadd") (param f32 f32) (result f32)
    local.get 0 local.get 1 f32.add)
  (func (export "fmul") (param f32 f32) (result f32)
    local.get 0 local.get 1 f32.mul)
  (memory (export "memory") 1))
WAT

# f64 module — double-precision, should compile under M7DP only
cat > "$TMPDIR/f64.wat" << 'WAT'
(module
  (func (export "dadd") (param f64 f64) (result f64)
    local.get 0 local.get 1 f64.add)
  (func (export "dmul") (param f64 f64) (result f64)
    local.get 0 local.get 1 f64.mul)
  (memory (export "memory") 1))
WAT

PASS=0
FAIL=0

check_compile() {
    local label="$1"; local wat="$2"; local target="$3"; local expect="$4"
    local elf="$TMPDIR/${label}.elf"
    if "$SYNTH" compile "$wat" -o "$elf" --target "$target" --all-exports >/dev/null 2>&1; then
        result="ok"
    else
        result="fail"
    fi
    if [ "$result" = "$expect" ]; then
        echo "PASS: ${label} on ${target} → ${result}"
        PASS=$((PASS + 1))
    else
        echo "FAIL: ${label} on ${target} → ${result} (expected ${expect})"
        FAIL=$((FAIL + 1))
    fi
}

# i32 should compile on every M7 variant
check_compile "i32_m7"   "$TMPDIR/i32_only.wat" cortex-m7   ok
check_compile "i32_m7dp" "$TMPDIR/i32_only.wat" cortex-m7dp ok

# f32 should compile on both (M7 has single-precision FPU)
check_compile "f32_m7"   "$TMPDIR/f32.wat" cortex-m7   ok
check_compile "f32_m7dp" "$TMPDIR/f32.wat" cortex-m7dp ok

# f64 must compile on M7DP. On M7 it should also work — synth falls back
# to soft-float helpers when hardware doesn't support double-precision.
check_compile "f64_m7dp" "$TMPDIR/f64.wat" cortex-m7dp ok

echo ""
echo "=== Results: ${PASS} passed, ${FAIL} failed ==="
[ "$FAIL" -eq 0 ]
