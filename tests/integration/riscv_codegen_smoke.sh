#!/bin/bash
# Smoke test: validate that synth's RV32IMAC codegen path produces a
# well-formed ELF for a representative i32 surface — arithmetic, comparisons,
# control flow (block/loop/if/br_if), and load/store.
#
# Companion to m7_codegen_smoke.sh on the ARM side. Network-free; suitable
# for CI.
#
# Usage:
#   bash tests/integration/riscv_codegen_smoke.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SYNTH="$PROJECT_ROOT/target/debug/synth"
TMPDIR="${TMPDIR:-/tmp}/synth_riscv_smoke_$$"

cleanup() { rm -rf "$TMPDIR"; }
trap cleanup EXIT
mkdir -p "$TMPDIR"

echo "=== Synth RISC-V codegen smoke test ==="

if [ ! -x "$SYNTH" ]; then
    (cd "$PROJECT_ROOT" && cargo build -p synth-cli --quiet)
fi

# Module 1: arithmetic + comparisons + locals
cat > "$TMPDIR/arith.wat" << 'WAT'
(module
  (memory (export "memory") 1)
  (func (export "add") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.add)
  (func (export "sub") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.sub)
  (func (export "mul") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.mul)
  (func (export "shl3") (param i32) (result i32)
    local.get 0 i32.const 3 i32.shl)
  (func (export "lt") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.lt_s)
  (func (export "ge") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.ge_s))
WAT

# Module 2: control flow (if/else, block, loop, br_if)
cat > "$TMPDIR/ctrl.wat" << 'WAT'
(module
  (memory (export "memory") 1)
  (func (export "max") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.gt_s
    if (result i32) (local.get 0)
    else (local.get 1)
    end))
WAT

# Module 3: division (must emit zero-trap guard)
cat > "$TMPDIR/div.wat" << 'WAT'
(module
  (memory (export "memory") 1)
  (func (export "divu") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.div_u)
  (func (export "rems") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.rem_s))
WAT

# Module 4: memory ops (load, store, sub-word access)
cat > "$TMPDIR/mem.wat" << 'WAT'
(module
  (memory (export "memory") 1)
  (func (export "load_word") (param i32) (result i32)
    local.get 0 i32.load offset=0)
  (func (export "store_word") (param i32 i32)
    local.get 0 local.get 1 i32.store offset=0)
  (func (export "load_byte_s") (param i32) (result i32)
    local.get 0 i32.load8_s offset=0)
  (func (export "store_byte") (param i32 i32)
    local.get 0 local.get 1 i32.store8 offset=0))
WAT

PASS=0
FAIL=0

check_compile() {
    local label="$1"; local wat="$2"
    local elf="$TMPDIR/${label}.elf"
    if "$SYNTH" compile "$wat" -o "$elf" --backend riscv --target riscv32imac --all-exports >/dev/null 2>&1; then
        # Verify the magic bytes say RISC-V and not ARM.
        local em
        em=$(xxd -s 18 -l 2 "$elf" | awk '{print $2}')
        if [ "$em" = "f300" ]; then
            echo "PASS: ${label} → EM_RISCV"
            PASS=$((PASS + 1))
        else
            echo "FAIL: ${label} → wrong machine type ($em, expected f300)"
            FAIL=$((FAIL + 1))
        fi
    else
        echo "FAIL: ${label} → compile error"
        FAIL=$((FAIL + 1))
    fi
}

check_compile "arith" "$TMPDIR/arith.wat"
check_compile "ctrl"  "$TMPDIR/ctrl.wat"
check_compile "div"   "$TMPDIR/div.wat"
check_compile "mem"   "$TMPDIR/mem.wat"

echo ""
echo "=== Results: ${PASS} passed, ${FAIL} failed ==="
[ "$FAIL" -eq 0 ]
