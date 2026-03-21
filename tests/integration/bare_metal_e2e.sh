#!/bin/bash
# End-to-end bare-metal cross-compilation test.
#
# Tests the complete pipeline:
#   WAT → synth compile → module.o → arm-none-eabi-gcc link → firmware.elf
#
# Prerequisites:
#   - cargo build -p synth-cli (synth binary in target/debug/)
#   - arm-none-eabi-gcc in PATH
#
# Usage:
#   bash tests/integration/bare_metal_e2e.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SYNTH="$PROJECT_ROOT/target/debug/synth"
STUB_C="$SCRIPT_DIR/kiln_builtins_stub.c"
TMPDIR="${TMPDIR:-/tmp}/synth_e2e_$$"

cleanup() { rm -rf "$TMPDIR"; }
trap cleanup EXIT
mkdir -p "$TMPDIR"

echo "=== Synth Bare-Metal End-to-End Test ==="
echo ""

# Check prerequisites
if ! command -v arm-none-eabi-gcc &>/dev/null; then
    echo "SKIP: arm-none-eabi-gcc not found in PATH"
    exit 0
fi

if [ ! -x "$SYNTH" ]; then
    echo "Building synth..."
    cargo build -p synth-cli --quiet
fi

# Step 1: Create test WAT module
cat > "$TMPDIR/test.wat" << 'WAT'
(module
  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add)
  (func (export "sub") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.sub)
  (func (export "mul") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.mul)
  (memory (export "memory") 1))
WAT
echo "[1/5] Created test.wat (add, sub, mul functions)"

# Step 2: Compile WAT to relocatable ELF
"$SYNTH" compile "$TMPDIR/test.wat" -o "$TMPDIR/module.o" --cortex-m --all-exports
echo "[2/5] Compiled to module.o ($(wc -c < "$TMPDIR/module.o") bytes)"

# Step 3: Compile kiln-builtins stub
arm-none-eabi-gcc -c -mcpu=cortex-m4 -mthumb -Os \
    "$STUB_C" -o "$TMPDIR/builtins.o"
echo "[3/5] Compiled kiln_builtins_stub.c ($(wc -c < "$TMPDIR/builtins.o") bytes)"

# Step 4: Link into firmware.elf using --link
"$SYNTH" compile "$TMPDIR/test.wat" -o "$TMPDIR/linked.o" \
    --cortex-m --all-exports --link --builtins "$TMPDIR/builtins.o"
FIRMWARE="$TMPDIR/linked.firmware.elf"
echo "[4/5] Linked firmware.elf ($(wc -c < "$FIRMWARE") bytes)"

# Step 5: Validate the ELF
echo "[5/5] Validating firmware.elf..."

# Check it's a valid ARM ELF
FILE_TYPE=$(file "$FIRMWARE")
if echo "$FILE_TYPE" | grep -q "ELF.*ARM"; then
    echo "  OK: Valid ARM ELF"
else
    echo "  FAIL: Not a valid ARM ELF: $FILE_TYPE"
    exit 1
fi

# Check for expected symbols
if command -v arm-none-eabi-nm &>/dev/null; then
    SYMBOLS=$(arm-none-eabi-nm "$FIRMWARE" 2>/dev/null || true)

    for sym in add sub mul __meld_dispatch_import __meld_get_memory_base; do
        if echo "$SYMBOLS" | grep -q "$sym"; then
            echo "  OK: Symbol '$sym' found"
        else
            echo "  WARN: Symbol '$sym' not found"
        fi
    done
fi

# Check for expected sections
if command -v arm-none-eabi-objdump &>/dev/null; then
    SECTIONS=$(arm-none-eabi-objdump -h "$FIRMWARE" 2>/dev/null || true)

    for sect in .text .data; do
        if echo "$SECTIONS" | grep -q "$sect"; then
            echo "  OK: Section '$sect' found"
        else
            echo "  WARN: Section '$sect' not found"
        fi
    done
fi

echo ""
echo "=== PASS ==="
echo "Firmware: $FIRMWARE"
echo "Size: $(wc -c < "$FIRMWARE") bytes"
