#!/usr/bin/env bash
# Integration test: compile WAT with imports to relocatable ARM ELF and validate.
#
# This test verifies the static linking PoC pipeline (M3):
#   1. synth compile succeeds for a module with imports
#   2. The output is a relocatable ELF (ET_REL, not ET_EXEC)
#   3. The import call is a direct `bl <field>`: a Thumb BL carrying an
#      R_ARM_THM_CALL relocation against the UNDEFINED symbol named by the
#      import's bare wasm field name (`log`), and no `__meld_dispatch_import`
#      (that fallback passed no wasm argument and was removed, #1699)
#   4. The ELF contains .rel.text relocation entries
#   5. The ELF contains a .meld_import_table metadata section
#   6. Exported function symbols are present
#   7. (Optional) If arm-none-eabi-ld is available, attempt a link
#
# Usage (via Bazel): bazel test //tests/integration:synth_static_link
# Usage (standalone): ./synth_static_link_test.sh  (with SYNTH and WAT env vars)

set -euo pipefail

# --- Locate test inputs via Bazel runfiles ---
if [[ -f "${RUNFILES_DIR:-/dev/null}/bazel_tools/tools/bash/runfiles/runfiles.bash" ]]; then
  # shellcheck disable=SC1090
  source "${RUNFILES_DIR}/bazel_tools/tools/bash/runfiles/runfiles.bash"
elif [[ -f "${BASH_RUNFILES:-/dev/null}" ]]; then
  # shellcheck disable=SC1090
  source "$BASH_RUNFILES"
else
  RUNFILES_DIR="${BASH_SOURCE[0]}.runfiles"
  if [[ -f "${RUNFILES_DIR}/bazel_tools/tools/bash/runfiles/runfiles.bash" ]]; then
    # shellcheck disable=SC1090
    source "${RUNFILES_DIR}/bazel_tools/tools/bash/runfiles/runfiles.bash"
  fi
fi

# Try Bazel runfiles first, fall back to environment variables
if type -t rlocation &>/dev/null; then
  SYNTH="$(rlocation "synth/crates/synth" 2>/dev/null)" || true
  WAT="$(rlocation "synth/tests/integration/import_call.wat" 2>/dev/null)" || true
fi

# Allow overriding via environment (for standalone testing)
SYNTH="${SYNTH:-}"
WAT="${WAT:-}"

if [[ -z "$SYNTH" || ! -x "$SYNTH" ]]; then
  echo "FAIL: synth binary not found or not executable at: ${SYNTH:-<unset>}" >&2
  echo "  Set SYNTH=/path/to/synth to run standalone." >&2
  exit 1
fi

if [[ -z "$WAT" || ! -f "$WAT" ]]; then
  echo "FAIL: WAT source file not found at: ${WAT:-<unset>}" >&2
  echo "  Set WAT=/path/to/import_call.wat to run standalone." >&2
  exit 1
fi

# --- Step 1: Compile WAT to relocatable ELF ---
OUTDIR="$(mktemp -d)"
trap 'rm -rf "$OUTDIR"' EXIT

ELF="$OUTDIR/import_call.o"

echo "=== M3 Static Linking PoC Test ==="
echo ""
echo "Compiling: $SYNTH compile $WAT -o $ELF --no-optimize"
if ! "$SYNTH" compile "$WAT" -o "$ELF" --no-optimize 2>&1; then
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
echo ""
echo "OK: ELF file created ($FILE_SIZE bytes)"

# --- Step 3: Validate ELF magic bytes ---
MAGIC=$(xxd -l 4 -p "$ELF")
if [[ "$MAGIC" != "7f454c46" ]]; then
  echo "FAIL: ELF magic bytes mismatch (got: $MAGIC, expected: 7f454c46)" >&2
  exit 1
fi
echo "OK: valid ELF magic bytes"

# --- Step 4: Verify it is a 32-bit little-endian ARM ELF ---
ELFCLASS=$(xxd -s 4 -l 1 -p "$ELF")
ELFDATA=$(xxd -s 5 -l 1 -p "$ELF")
if [[ "$ELFCLASS" != "01" ]]; then
  echo "FAIL: expected 32-bit ELF (EI_CLASS=01), got EI_CLASS=$ELFCLASS" >&2
  exit 1
fi
echo "OK: 32-bit ELF"

if [[ "$ELFDATA" != "01" ]]; then
  echo "FAIL: expected little-endian ELF (EI_DATA=01), got EI_DATA=$ELFDATA" >&2
  exit 1
fi
echo "OK: little-endian ELF"

# e_machine = ARM (0x28 = 40)
E_MACHINE=$(xxd -s 18 -l 2 -p "$ELF")
if [[ "$E_MACHINE" != "2800" ]]; then
  echo "FAIL: expected ARM ELF (e_machine=2800), got e_machine=$E_MACHINE" >&2
  exit 1
fi
echo "OK: ARM architecture"

# --- Step 5: Verify ELF type is ET_REL (1) ---
# e_type is at offset 16, 2 bytes, little-endian
E_TYPE=$(xxd -s 16 -l 2 -p "$ELF")
if [[ "$E_TYPE" != "0100" ]]; then
  echo "FAIL: expected relocatable ELF (e_type=0100/ET_REL), got e_type=$E_TYPE" >&2
  exit 1
fi
echo "OK: relocatable ELF (ET_REL)"

# --- Step 6: The import call is a direct `bl log` against the undefined `log` ---
# Read from the ELF itself (section headers -> SHT_REL -> symtab -> strtab),
# with od only, so the check needs no cross toolchain. ELF32 little-endian
# was established in step 4. Two objects are checked:
#   - the one compiled above (no --target: A32 code, so the call is an A32
#     BL carrying R_ARM_CALL), and
#   - the same module for cortex-m4 (Thumb-2: a Thumb BL carrying
#     R_ARM_THM_CALL), the form a Cortex-M embedder links.
IMPORT_FIELD="log"
R_ARM_THM_CALL=10
R_ARM_CALL=28
SHT_REL=9

# check_import_call <elf> <expected relocation type> <label>
check_import_call() {
  local elf="$1" want_type="$2" label="$3"
  rd32() { od -An -tu4 -j "$1" -N4 "$elf" | tr -d ' \n'; }
  rd16() { od -An -tu2 -j "$1" -N2 "$elf" | tr -d ' \n'; }
  # LC_ALL=C: the bytes after the name are not text in any locale.
  cstr() { tail -c "+$(( $1 + 1 ))" "$elf" | head -c 256 | LC_ALL=C tr '\0' '\n' | head -n 1; }
  local e_shoff e_shentsize e_shnum
  e_shoff=$(rd32 32); e_shentsize=$(rd16 46); e_shnum=$(rd16 48)
  sh_field() { rd32 $(( e_shoff + $1 * e_shentsize + $2 )); }   # section, field offset
  local import_calls=0 other_external="" i r
  for (( i = 0; i < e_shnum; i++ )); do
    [[ "$(sh_field "$i" 4)" -eq $SHT_REL ]] || continue
    local rel_off rel_size symtab target sym_off strtab str_off text_off
    rel_off=$(sh_field "$i" 16); rel_size=$(sh_field "$i" 20)
    symtab=$(sh_field "$i" 24);  target=$(sh_field "$i" 28)
    sym_off=$(sh_field "$symtab" 16); strtab=$(sh_field "$symtab" 24)
    str_off=$(sh_field "$strtab" 16); text_off=$(sh_field "$target" 16)
    for (( r = 0; r < rel_size / 8; r++ )); do
      local r_offset r_info r_type r_sym st_name st_shndx name is_bl=0
      r_offset=$(rd32 $(( rel_off + r * 8 )))
      r_info=$(rd32 $(( rel_off + r * 8 + 4 )))
      r_type=$(( r_info & 0xff )); r_sym=$(( r_info >> 8 ))
      st_name=$(rd32 $(( sym_off + r_sym * 16 )))
      st_shndx=$(rd16 $(( sym_off + r_sym * 16 + 14 )))
      [[ "$st_shndx" -eq 0 ]] || continue          # defined: an internal call
      name=$(cstr $(( str_off + st_name )))
      if [[ "$want_type" -eq $R_ARM_THM_CALL ]]; then
        local hw1 hw2
        hw1=$(rd16 $(( text_off + r_offset ))); hw2=$(rd16 $(( text_off + r_offset + 2 )))
        [[ $(( hw1 & 0xF800 )) -eq $(( 0xF000 )) && $(( hw2 & 0xD000 )) -eq $(( 0xD000 )) ]] && is_bl=1
      else
        local word
        word=$(rd32 $(( text_off + r_offset )))
        [[ $(( word & 0x0F000000 )) -eq $(( 0x0B000000 )) ]] && is_bl=1
      fi
      if [[ "$name" == "$IMPORT_FIELD" && "$r_type" -eq "$want_type" && "$is_bl" -eq 1 ]]; then
        import_calls=$(( import_calls + 1 ))
      else
        other_external="$other_external $name(type $r_type, bl=$is_bl)"
      fi
    done
  done
  if [[ "$import_calls" -ge 1 && -z "$other_external" ]]; then
    echo "OK: $label: $import_calls import call(s) are \`bl $IMPORT_FIELD\` (relocation type $want_type, undefined \`$IMPORT_FIELD\`)"
  else
    echo "FAIL: $label: expected every external relocation to be a BL with relocation type" >&2
    echo "  $want_type against the undefined symbol \`$IMPORT_FIELD\`; found $import_calls such call(s)" >&2
    echo "  and other external relocations:${other_external:- none}" >&2
    exit 1
  fi
  if xxd -p "$elf" | tr -d '\n' | grep -qi "$(echo -n '__meld_dispatch_import' | xxd -p)"; then
    echo "FAIL: $label: __meld_dispatch_import is still referenced by the object (#1699)" >&2
    exit 1
  fi
  echo "OK: $label: no __meld_dispatch_import in the object"
}

check_import_call "$ELF" $R_ARM_CALL "default target (A32)"

ELF_M4="$OUTDIR/import_call_m4.o"
echo "Compiling: $SYNTH compile $WAT -o $ELF_M4 --target cortex-m4"
if ! "$SYNTH" compile "$WAT" -o "$ELF_M4" --target cortex-m4 >/dev/null 2>&1; then
  echo "FAIL: synth compile --target cortex-m4 exited with non-zero status" >&2
  exit 1
fi
if [[ "$(xxd -s 16 -l 2 -p "$ELF_M4")" != "0100" ]]; then
  echo "FAIL: the cortex-m4 output is not a relocatable ELF (ET_REL)" >&2
  exit 1
fi
check_import_call "$ELF_M4" $R_ARM_THM_CALL "cortex-m4 (Thumb-2)"

# --- Step 7: Check for call_log exported function symbol ---
if xxd -p "$ELF" | tr -d '\n' | grep -qi "$(echo -n 'call_log' | xxd -p)"; then
  echo "OK: call_log function symbol found"
else
  echo "FAIL: call_log function symbol NOT found in ELF" >&2
  exit 1
fi

# --- Step 8: Check for .rel.text section ---
# The string ".rel.text" should appear in the section header string table
if xxd -p "$ELF" | tr -d '\n' | grep -qi "$(echo -n '.rel.text' | xxd -p)"; then
  echo "OK: .rel.text relocation section found"
else
  echo "FAIL: .rel.text section NOT found in ELF" >&2
  exit 1
fi

# --- Step 9: Check for .meld_import_table section ---
if xxd -p "$ELF" | tr -d '\n' | grep -qi "$(echo -n '.meld_import_table' | xxd -p)"; then
  echo "OK: .meld_import_table metadata section found"
else
  echo "FAIL: .meld_import_table section NOT found in ELF" >&2
  exit 1
fi

# --- Step 10: Verify import metadata contains "env" and "log" ---
if xxd -p "$ELF" | tr -d '\n' | grep -qi "$(echo -n 'env' | xxd -p)"; then
  echo "OK: import module name 'env' found in metadata"
else
  echo "WARN: import module name 'env' not found (may be OK if metadata format differs)"
fi

if xxd -p "$ELF" | tr -d '\n' | grep -qi "$(echo -n 'log' | xxd -p)"; then
  echo "OK: import field name 'log' found in metadata"
else
  echo "WARN: import field name 'log' not found (may be OK if metadata format differs)"
fi

# --- Step 11 (Optional): Try actual link if ARM toolchain is available ---
echo ""
if command -v arm-none-eabi-ld &>/dev/null; then
  echo "=== ARM toolchain detected — attempting static link ==="

  # Create a minimal embedder stub that provides the imported function
  STUB_S="$OUTDIR/bridge_stub.s"
  STUB_O="$OUTDIR/bridge_stub.o"
  FIRMWARE="$OUTDIR/firmware.elf"

  cat > "$STUB_S" << 'STUBEOF'
  .syntax unified
  .cpu cortex-m4
  .thumb
  .global log
  .type log, %function
log:
  bx lr
STUBEOF

  if command -v arm-none-eabi-as &>/dev/null; then
    arm-none-eabi-as -mcpu=cortex-m4 -mthumb "$STUB_S" -o "$STUB_O" 2>&1 || true
    if [[ -f "$STUB_O" ]]; then
      echo "OK: bridge stub assembled"
      if arm-none-eabi-ld --entry=0 -o "$FIRMWARE" "$ELF_M4" "$STUB_O" 2>&1; then
        echo "OK: static link succeeded — firmware at $FIRMWARE ($(wc -c < "$FIRMWARE" | tr -d ' ') bytes)"
      else
        echo "WARN: link step failed (expected if linker script is needed)"
      fi
    fi
  else
    echo "SKIP: arm-none-eabi-as not found, cannot assemble bridge stub"
  fi
else
  echo "SKIP: arm-none-eabi-ld not found — cross-linking not tested"
  echo "  Install with: brew install arm-none-eabi-gcc (macOS)"
fi

echo ""
echo "PASS: all static linking PoC checks passed"
