#!/bin/bash
# Fetch OSxCAR anti-pinch WASM components from https://osxcar.de/insights/demonstration/
# and compile them through synth to verify end-to-end real-world compilation.
#
# The OSxCAR demo is an automotive anti-pinch window controller that runs
# the same WASM binaries in the browser and on a target ECU. The WASM modules
# are base64-encoded in the JavaScript component files.
#
# Usage:
#   bash tests/integration/fetch_osxcar_wasm.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SYNTH="$PROJECT_ROOT/target/debug/synth"
TMPDIR="${TMPDIR:-/tmp}/synth_osxcar_$$"

cleanup() { rm -rf "$TMPDIR"; }
trap cleanup EXIT
mkdir -p "$TMPDIR"

echo "=== OSxCAR Anti-Pinch WASM Compilation Test ==="
echo ""

# Check prerequisites
if ! command -v curl &>/dev/null; then
    echo "SKIP: curl not found"
    exit 0
fi

if ! command -v python3 &>/dev/null; then
    echo "SKIP: python3 not found"
    exit 0
fi

if [ ! -x "$SYNTH" ]; then
    echo "Building synth..."
    (cd "$PROJECT_ROOT" && cargo build -p synth-cli --quiet)
fi

BASE_URL="https://osxcar.de/js/anti-pinch/components/html"

# Extract WASM from base64-encoded JavaScript components
extract_wasm() {
    local js_file="$1"
    local output="$2"
    local url="${BASE_URL}/${js_file}"

    curl -sL "$url" | python3 -c "
import sys, base64, re
content = sys.stdin.read()
matches = re.findall(r\"base64Compile\('([A-Za-z0-9+/=]+)'\)\", content)
if not matches:
    print('ERROR: No WASM module found', file=sys.stderr)
    sys.exit(1)
m = matches[0]
padding = 4 - len(m) % 4
if padding != 4:
    m += '=' * padding
data = base64.b64decode(m)
if data[:4] != b'\x00asm':
    print('ERROR: Not a valid WASM module', file=sys.stderr)
    sys.exit(1)
open('$output', 'wb').write(data)
print(f'{len(data)} bytes')
"
}

PASS=0
FAIL=0

# OSxCAR modules use f64 (double-precision) math internally.
# Cortex-M7DP has a double-precision FPU; Cortex-M4F only has single-precision.
# Use --target cortex-m7dp to enable f64 hardware support.
TARGET="cortex-m7dp"

# Fetch and compile each component
for component in anti_pinch_v2_component motor_driver_v2_component soft_start_stop_component; do
    echo -n "[fetch] ${component}.js → "
    WASM="$TMPDIR/${component}.wasm"

    if ! extract_wasm "${component}.js" "$WASM" 2>/dev/null; then
        echo "FAIL (fetch)"
        FAIL=$((FAIL + 1))
        continue
    fi

    echo -n "$(wc -c < "$WASM" | tr -d ' ') bytes → "

    # Compile through synth with double-precision FPU target
    ELF="$TMPDIR/${component}.elf"
    if "$SYNTH" compile "$WASM" -o "$ELF" --target "$TARGET" --all-exports 2>/dev/null; then
        FUNCS=$(grep -c "INFO.*bytes of machine code" <<< "$("$SYNTH" compile "$WASM" -o "$ELF" --target "$TARGET" --all-exports 2>&1)" || echo "?")
        echo "OK ($(wc -c < "$ELF" | tr -d ' ') byte ELF, target: ${TARGET})"
        PASS=$((PASS + 1))
    else
        echo "FAIL (compile)"
        FAIL=$((FAIL + 1))
    fi
done

echo ""
echo "=== Results: ${PASS} passed, ${FAIL} failed ==="

if [ "$FAIL" -gt 0 ]; then
    exit 1
fi
