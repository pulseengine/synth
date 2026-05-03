#!/bin/bash
# RISC-V calculator demo — end-to-end pipeline test.
#
# Pipeline:
#   examples/calculator/calculator.wat
#     → synth compile --backend riscv → calculator.o (RV32 EM_RISCV ELF)
#     → synth riscv-runtime → startup.c + linker.ld
#     → riscv64-unknown-elf-gcc (if present) → firmware.elf
#
# This is the B4 deliverable: prove the full RISC-V toolchain produces a
# bootable firmware ELF for a representative WASM module.
#
# When `riscv64-unknown-elf-gcc` is missing, the test still validates that:
#   1. synth compiles the calculator to RV32IMAC bytes correctly.
#   2. All 5 calculator functions show up in the symbol table.
#   3. The startup + linker script generators emit syntactically plausible
#      output.
#
# When the toolchain is present, the script links a full firmware ELF.
#
# Usage:
#   bash tests/integration/riscv_calculator_demo.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SYNTH="$PROJECT_ROOT/target/debug/synth"
TMPDIR="${TMPDIR:-/tmp}/synth_rv_calc_$$"

cleanup() { rm -rf "$TMPDIR"; }
trap cleanup EXIT
mkdir -p "$TMPDIR"

echo "=== Synth RISC-V calculator demo ==="

if [ ! -x "$SYNTH" ]; then
    (cd "$PROJECT_ROOT" && cargo build -p synth-cli --quiet)
fi

WAT="$PROJECT_ROOT/examples/calculator/calculator.wat"
if [ ! -f "$WAT" ]; then
    echo "FAIL: calculator.wat missing at $WAT"
    exit 1
fi

# Step 1 — compile WAT to RISC-V .o
echo "[1/4] Compiling calculator.wat for riscv32imac..."
"$SYNTH" compile "$WAT" -o "$TMPDIR/calculator.o" \
    --backend riscv --target riscv32imac --all-exports >/dev/null 2>&1
ELF_TYPE="$(file "$TMPDIR/calculator.o")"
case "$ELF_TYPE" in
    *RISC-V*) echo "    OK: $ELF_TYPE" ;;
    *) echo "    FAIL: not RISC-V (got: $ELF_TYPE)"; exit 1 ;;
esac

# Step 2 — verify all 5 calculator symbols are present
echo "[2/4] Checking calculator symbols..."
EXPECTED_SYMS="add subtract multiply divide modulo"
ALL_OK=1
for sym in $EXPECTED_SYMS; do
    if grep -aq "$sym" "$TMPDIR/calculator.o"; then
        echo "    OK: $sym"
    else
        echo "    FAIL: $sym not found in symbol table"
        ALL_OK=0
    fi
done
[ "$ALL_OK" -eq 1 ] || exit 1

# Step 3 — emit startup + linker script
echo "[3/4] Generating runtime (startup.c + linker.ld)..."
"$SYNTH" riscv-runtime -o "$TMPDIR/runtime" --target rv32imac >/dev/null
[ -f "$TMPDIR/runtime/startup.c" ] || { echo "    FAIL: startup.c not written"; exit 1; }
[ -f "$TMPDIR/runtime/linker.ld" ] || { echo "    FAIL: linker.ld not written"; exit 1; }

# Verify the startup file contains the RV-specific bits.
for marker in "csrw mtvec" "_reset" "_trap_entry" "synth_trap_handler" "la s11"; do
    if ! grep -q "$marker" "$TMPDIR/runtime/startup.c"; then
        echo "    FAIL: startup.c missing '$marker'"
        exit 1
    fi
done
echo "    OK: startup.c contains all required RV-specific markers"

# Verify the linker script produces flash+ram regions and the entry point.
for marker in 'OUTPUT_ARCH("riscv")' 'ENTRY(_reset)' '_stack_top' '__linear_memory_base' '__global_pointer$'; do
    if ! grep -F -q "$marker" "$TMPDIR/runtime/linker.ld"; then
        echo "    FAIL: linker.ld missing '$marker'"
        exit 1
    fi
done
echo "    OK: linker.ld contains all required sections + symbols"

# Step 4 — optional full link with the cross-toolchain
echo "[4/4] Cross-link to firmware (optional — needs riscv64-unknown-elf-gcc)..."
if command -v riscv64-unknown-elf-gcc >/dev/null 2>&1; then
    riscv64-unknown-elf-gcc \
        -nostartfiles -nostdlib \
        -mabi=ilp32 -march=rv32imac \
        -T "$TMPDIR/runtime/linker.ld" \
        -o "$TMPDIR/firmware.elf" \
        "$TMPDIR/runtime/startup.c" \
        "$TMPDIR/calculator.o"
    SIZE="$(wc -c < "$TMPDIR/firmware.elf")"
    echo "    OK: firmware.elf is $SIZE bytes"
    echo "    file: $(file "$TMPDIR/firmware.elf")"
else
    echo "    SKIP: riscv64-unknown-elf-gcc not in PATH (this is fine on dev hosts)"
fi

echo ""
echo "=== Calculator demo: PASS ==="
