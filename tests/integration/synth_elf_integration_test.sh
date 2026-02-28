#!/usr/bin/env bash
# Integration test: compile WAT to ARM ELF and validate the output.
#
# This test verifies the end-to-end compilation pipeline:
#   1. synth compile succeeds (exit code 0)
#   2. The output file exists and is non-empty
#   3. The output file starts with the ELF magic bytes (7f 45 4c 46)
#   4. The output is a 32-bit little-endian ARM ELF
#
# Usage (via Bazel): bazel test //tests/integration:synth_elf_integration

set -euo pipefail

# --- Locate test inputs via Bazel runfiles ---
# https://github.com/bazelbuild/bazel/blob/master/tools/bash/runfiles/runfiles.bash
# shellcheck disable=SC1090
if [[ -f "${RUNFILES_DIR:-/dev/null}/bazel_tools/tools/bash/runfiles/runfiles.bash" ]]; then
  source "${RUNFILES_DIR}/bazel_tools/tools/bash/runfiles/runfiles.bash"
elif [[ -f "${BASH_RUNFILES:-/dev/null}" ]]; then
  source "$BASH_RUNFILES"
else
  # Fallback: find runfiles relative to the script
  RUNFILES_DIR="${BASH_SOURCE[0]}.runfiles"
  if [[ -f "${RUNFILES_DIR}/bazel_tools/tools/bash/runfiles/runfiles.bash" ]]; then
    source "${RUNFILES_DIR}/bazel_tools/tools/bash/runfiles/runfiles.bash"
  else
    echo "FAIL: cannot find Bazel bash runfiles library" >&2
    exit 1
  fi
fi

SYNTH="$(rlocation "synth/crates/synth")" || true
WAT="$(rlocation "synth/tests/integration/add.wat")" || true

if [[ -z "${SYNTH:-}" || ! -x "$SYNTH" ]]; then
  echo "FAIL: synth binary not found or not executable at: ${SYNTH:-<unset>}" >&2
  exit 1
fi

if [[ -z "${WAT:-}" || ! -f "$WAT" ]]; then
  echo "FAIL: WAT source file not found at: ${WAT:-<unset>}" >&2
  exit 1
fi

# --- Step 1: Compile WAT to ELF ---
OUTDIR="$(mktemp -d)"
trap 'rm -rf "$OUTDIR"' EXIT

ELF="$OUTDIR/output.elf"

echo "Compiling: $SYNTH compile $WAT -o $ELF --cortex-m"
if ! "$SYNTH" compile "$WAT" -o "$ELF" --cortex-m; then
  echo "FAIL: synth compile exited with non-zero status" >&2
  exit 1
fi

# --- Step 2: Check output file exists and is non-empty ---
if [[ ! -f "$ELF" ]]; then
  echo "FAIL: output ELF file was not created" >&2
  exit 1
fi

FILE_SIZE=$(wc -c < "$ELF" | tr -d ' ')
if [[ "$FILE_SIZE" -eq 0 ]]; then
  echo "FAIL: output ELF file is empty (0 bytes)" >&2
  exit 1
fi
echo "OK: ELF file created ($FILE_SIZE bytes)"

# --- Step 3: Validate ELF magic bytes ---
# The first 4 bytes of any ELF file must be: 7f 45 4c 46 (\x7fELF)
MAGIC=$(xxd -l 4 -p "$ELF")
if [[ "$MAGIC" != "7f454c46" ]]; then
  echo "FAIL: ELF magic bytes mismatch (got: $MAGIC, expected: 7f454c46)" >&2
  exit 1
fi
echo "OK: valid ELF magic bytes"

# --- Step 4: Verify it is a 32-bit little-endian ARM ELF ---
# Byte 5 (EI_CLASS): 01 = 32-bit
# Byte 6 (EI_DATA):  01 = little-endian
ELFCLASS=$(xxd -s 4 -l 1 -p "$ELF")
ELFDATA=$(xxd -s 5 -l 1 -p "$ELF")
if [[ "$ELFCLASS" != "01" ]]; then
  echo "FAIL: expected 32-bit ELF (EI_CLASS=01), got EI_CLASS=$ELFCLASS" >&2
  exit 1
fi
echo "OK: 32-bit ELF (EI_CLASS=$ELFCLASS)"

if [[ "$ELFDATA" != "01" ]]; then
  echo "FAIL: expected little-endian ELF (EI_DATA=01), got EI_DATA=$ELFDATA" >&2
  exit 1
fi
echo "OK: little-endian ELF (EI_DATA=$ELFDATA)"

# Bytes 18-19 (e_machine): 0x28 (40) = ARM, little-endian = 2800
E_MACHINE=$(xxd -s 18 -l 2 -p "$ELF")
if [[ "$E_MACHINE" != "2800" ]]; then
  echo "FAIL: expected ARM ELF (e_machine=2800), got e_machine=$E_MACHINE" >&2
  exit 1
fi
echo "OK: ARM architecture (e_machine=$E_MACHINE)"

echo ""
echo "PASS: all ELF integration checks passed"
