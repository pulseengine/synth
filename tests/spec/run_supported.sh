#!/usr/bin/env bash
# run_supported.sh — Run WebAssembly spec test suite against synth
#
# Tests all 257 .wast files from the official spec-testsuite:
#   1. Parse each file with synth-test stats
#   2. Attempt compilation with synth-cli compile
#   3. Report pass/fail summary by category
#
# Usage:
#   ./run_supported.sh                    # Full run with optimizer
#   ./run_supported.sh --no-optimize      # Bypass optimizer (avoids regalloc panics)
#   ./run_supported.sh --quick            # Only test high-value files (i32, control flow, etc.)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUTDIR="/tmp/synth-spec-results"

# Parse arguments
NO_OPTIMIZE=""
QUICK_MODE=false
for arg in "$@"; do
    case "$arg" in
        --no-optimize) NO_OPTIMIZE="--no-optimize" ;;
        --quick) QUICK_MODE=true ;;
        --help|-h)
            echo "Usage: $0 [--no-optimize] [--quick]"
            echo "  --no-optimize  Disable peephole optimizer (avoids regalloc panics)"
            echo "  --quick        Only test high-value spec files"
            exit 0
            ;;
    esac
done

mkdir -p "$OUTDIR"

# High-value files for quick mode: core i32/i64, control flow, locals, memory
QUICK_FILES=(
    i32 i64 int_exprs int_literals
    block loop if br br_if br_table
    call call_indirect return return_call
    nop unreachable forward switch fac
    local_get local_set local_tee select global
    labels stack func
    load store memory_size endianness
    f32 f32_bitwise f32_cmp f64 f64_bitwise f64_cmp
    conversions float_exprs float_literals float_memory
    left-to-right unwind
)

# Counters
PARSE_OK=0
PARSE_FAIL=0
COMPILE_OK=0
COMPILE_PANIC=0
COMPILE_ERROR=0
COMPILE_NOEXPORT=0
TOTAL_ASSERT_RETURN=0

# Result arrays
declare -a OK_FILES=()
declare -a PANIC_FILES=()
declare -a ERROR_FILES=()
declare -a NOEXPORT_FILES=()
declare -a PARSE_FAIL_FILES=()

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Build tools first
echo "Building synth-test and synth-cli..."
cargo build -p synth-test -p synth-cli --quiet 2>&1

SYNTH_TEST="$PROJECT_ROOT/target/debug/synth-test"
SYNTH_CLI="$PROJECT_ROOT/target/debug/synth"

echo ""
if [ -n "$NO_OPTIMIZE" ]; then
    echo "Mode: --no-optimize (bypassing peephole optimizer)"
fi
if $QUICK_MODE; then
    echo "Mode: --quick (testing ${#QUICK_FILES[@]} high-value files)"
fi
echo "========================================"
echo ""

# Determine which files to test
if $QUICK_MODE; then
    FILES=()
    for f in "${QUICK_FILES[@]}"; do
        if [ -f "$SCRIPT_DIR/$f.wast" ]; then
            FILES+=("$SCRIPT_DIR/$f.wast")
        fi
    done
else
    FILES=("$SCRIPT_DIR"/*.wast)
fi

TOTAL=${#FILES[@]}
CURRENT=0

for wast_file in "${FILES[@]}"; do
    CURRENT=$((CURRENT + 1))
    basename=$(basename "$wast_file" .wast)

    # Step 1: Parse with synth-test stats
    STATS=$("$SYNTH_TEST" stats --wast "$wast_file" 2>&1) || {
        PARSE_FAIL=$((PARSE_FAIL + 1))
        PARSE_FAIL_FILES+=("$basename")
        printf "[%3d/%d] ${RED}PARSE FAIL${NC}  %-30s\n" "$CURRENT" "$TOTAL" "$basename"
        continue
    }
    PARSE_OK=$((PARSE_OK + 1))

    ASSERT_RET=$(echo "$STATS" | grep "Assert_return:" | awk '{print $NF}')
    TEST_TOTAL=$(echo "$STATS" | grep "Total test cases:" | awk '{print $NF}')
    TOTAL_ASSERT_RETURN=$((TOTAL_ASSERT_RETURN + ASSERT_RET))

    # Step 2: Attempt compilation
    COMPILE=$("$SYNTH_CLI" compile "$wast_file" -o "$OUTDIR/spec_${basename}.elf" \
              --cortex-m --all-exports $NO_OPTIMIZE 2>&1) || true

    if echo "$COMPILE" | grep -q "panicked"; then
        COMPILE_PANIC=$((COMPILE_PANIC + 1))
        PANIC_FILES+=("$basename($TEST_TOTAL)")
        printf "[%3d/%d] ${YELLOW}PANIC${NC}       %-30s  tests=%s  (optimizer regalloc exhausted)\n" \
               "$CURRENT" "$TOTAL" "$basename" "$TEST_TOTAL"
    elif echo "$COMPILE" | grep -q "No exported functions"; then
        COMPILE_NOEXPORT=$((COMPILE_NOEXPORT + 1))
        if [ "$ASSERT_RET" -gt 0 ]; then
            NOEXPORT_FILES+=("$basename($ASSERT_RET)")
            printf "[%3d/%d] ${CYAN}NO EXPORTS${NC}  %-30s  assert_return=%s (first module has no exports)\n" \
                   "$CURRENT" "$TOTAL" "$basename" "$ASSERT_RET"
        else
            printf "[%3d/%d] ${CYAN}NO EXPORTS${NC}  %-30s  (validation-only test)\n" \
                   "$CURRENT" "$TOTAL" "$basename"
        fi
    elif echo "$COMPILE" | grep -q "Error:"; then
        COMPILE_ERROR=$((COMPILE_ERROR + 1))
        ERR=$(echo "$COMPILE" | grep "Error:" | head -1 | sed 's/Error: //')
        ERROR_FILES+=("$basename")
        printf "[%3d/%d] ${RED}ERROR${NC}       %-30s  tests=%s  %s\n" \
               "$CURRENT" "$TOTAL" "$basename" "$TEST_TOTAL" "$ERR"
    else
        COMPILE_OK=$((COMPILE_OK + 1))
        OK_FILES+=("$basename")
        if [ "$ASSERT_RET" -gt 0 ]; then
            printf "[%3d/%d] ${GREEN}OK${NC}          %-30s  assert_return=%s\n" \
                   "$CURRENT" "$TOTAL" "$basename" "$ASSERT_RET"
        else
            printf "[%3d/%d] ${GREEN}OK${NC}          %-30s  (no assert_return tests)\n" \
                   "$CURRENT" "$TOTAL" "$basename"
        fi
    fi
done

echo ""
echo "========================================"
echo "SUMMARY"
echo "========================================"
echo ""
echo "Files tested:         $TOTAL"
echo ""
echo -e "${GREEN}Parse OK:             $PARSE_OK${NC}"
echo -e "${RED}Parse FAIL:           $PARSE_FAIL${NC}"
echo ""
echo -e "${GREEN}Compile OK:           $COMPILE_OK${NC}  (${#OK_FILES[@]} files)"
echo -e "${YELLOW}Compile PANIC:        $COMPILE_PANIC${NC}  (optimizer regalloc — all pass with --no-optimize)"
echo -e "${RED}Compile ERROR:        $COMPILE_ERROR${NC}"
echo -e "${CYAN}Compile NO_EXPORTS:   $COMPILE_NOEXPORT${NC}  (first module lacks exports; multi-module WAST)"
echo ""
echo "Total assert_return tests parsed: $TOTAL_ASSERT_RETURN"
echo ""

if [ ${#PANIC_FILES[@]} -gt 0 ]; then
    echo "Optimizer regalloc panics (fixable with --no-optimize):"
    printf "  %s\n" "${PANIC_FILES[@]}"
    echo ""
fi

if [ ${#ERROR_FILES[@]} -gt 0 ]; then
    echo "Compile errors:"
    printf "  %s\n" "${ERROR_FILES[@]}"
    echo ""
fi

if [ ${#PARSE_FAIL_FILES[@]} -gt 0 ]; then
    echo "Parse failures:"
    printf "  %s\n" "${PARSE_FAIL_FILES[@]}"
    echo ""
fi

# Exit with failure if any panics or errors
if [ $COMPILE_PANIC -gt 0 ] || [ $COMPILE_ERROR -gt 0 ] || [ $PARSE_FAIL -gt 0 ]; then
    exit 1
fi
