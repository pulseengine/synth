#!/usr/bin/env bash
# RQ-57-MCDC (#912) — build the row-driver harness for wasm32-wasip1, run every
# truth-table row under `witness`, and write the MC/DC report.
#
# TWO INVOCATION TRAPS this script exists to make unreachable (both documented
# on #912 and filed upstream as pulseengine/witness#177 / #178):
#
#   1. `witness report` WITHOUT `--format mcdc` prints branches *reached*, not
#      MC/DC. That number looks like coverage, is not, and is how this step got
#      read as "nothing here" for six releases. We always ask for `mcdc` and
#      `mcdc-json`.
#   2. A build without full DWARF renders every gap row `(anon)` and untriageable
#      while still reporting `attribution_source: "dwarf"`. We always build with
#      `-C debuginfo=2` and the dev profile (a `--release` build at opt-level
#      z/s dead-strips witness's counters).
#
# Usage: scripts/mcdc_run.sh [output-dir]
set -euo pipefail

OUT=${1:-target/mcdc}
REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$REPO"
mkdir -p "$OUT"

WITNESS=${WITNESS:-witness-mcdc}
command -v "$WITNESS" >/dev/null || {
  echo "error: $WITNESS not on PATH (install from pulseengine/witness releases)" >&2
  exit 127
}

# Dev profile + full debuginfo: see trap 2 above.
RUSTFLAGS="-C debuginfo=2 ${RUSTFLAGS:-}" \
  cargo build --target wasm32-wasip1 -p synth-mcdc-harness

WASM=$(cargo metadata --format-version 1 --no-deps \
  | python3 -c 'import json,sys; print(json.load(sys.stdin)["target_directory"])')/wasm32-wasip1/debug/synth_mcdc_harness.wasm
test -f "$WASM" || { echo "error: harness wasm not found at $WASM" >&2; exit 1; }

"$WITNESS" instrument "$WASM" -o "$OUT/instrumented.wasm"

# ── The truth-table rows ────────────────────────────────────────────────────
# Each `--invoke-with-args` is ONE row. The vectors are chosen for unique-cause
# / masking MC/DC on the decisions named in the harness doc comments, not for a
# percentage. Adding a row here is how a gap row gets closed.
"$WITNESS" run "$OUT/instrumented.wasm" \
  `# static_data_addr::resolve_owner — c >= off && c < off + len.` \
  `# ONE segment so the membership test is evaluated exactly once per` \
  `# invocation (witness records one row per invocation; a decision inside a` \
  `# loop collapses to a single captured vector).` \
  --invoke-with-args 'sd_resolve_owner:80,1,1' \
  --invoke-with-args 'sd_resolve_owner:255,1,1' \
  --invoke-with-args 'sd_resolve_owner:256,1,1' \
  --invoke-with-args 'sd_resolve_owner:258,1,1' \
  --invoke-with-args 'sd_resolve_owner:259,1,1' \
  --invoke-with-args 'sd_resolve_owner:260,1,1' \
  --invoke-with-args 'sd_resolve_owner:512,1,1' \
  --invoke-with-args 'sd_resolve_owner:80,0,1' \
  --invoke-with-args 'sd_resolve_owner:256,0,1' \
  --invoke-with-args 'sd_resolve_owner:512,0,1' \
  `# the #757 overlapping shape — behaviour, not vectors` \
  --invoke-with-args 'sd_resolve_owner:256,1,2' \
  --invoke-with-args 'sd_resolve_owner:256,0,2' \
  `# validate_reloc_resolutions_spanned — j == 0 && seg_byte != runtime_byte` \
  --invoke-with-args 'sd_validate_spanned:1,0' \
  --invoke-with-args 'sd_validate_spanned:0,0' \
  --invoke-with-args 'sd_validate_spanned:1,2' \
  --invoke-with-args 'sd_validate_spanned:0,3' \
  --invoke-with-args 'sd_validate_spanned:1,3' \
  `# out-of-range emitted resolutions — both let-else rejects` \
  --invoke-with-args 'sd_validate_spanned:9,0' \
  --invoke-with-args 'sd_validate_spanned:1,99' \
  `# validate_served_image — addr >= image.len() && owed != 0` \
  --invoke-with-args 'sd_validate_served:4,0' \
  --invoke-with-args 'sd_validate_served:0,0' \
  --invoke-with-args 'sd_validate_served:4,1' \
  --invoke-with-args 'sd_validate_served:2,1' \
  --invoke-with-args 'sd_validate_served:1,0' \
  --invoke-with-args 'sd_validate_served:0,1' \
  `# alloc_validator::validate_final_allocation_rv32 (VCR-RA-003 / #871)` \
  --invoke-with-args 'ra_validate:0' \
  --invoke-with-args 'ra_validate:1' \
  --invoke-with-args 'ra_validate:2' \
  --invoke-with-args 'ra_validate:3' \
  --invoke-with-args 'ra_validate:4' \
  --invoke-with-args 'ra_validate:5' \
  --invoke-with-args 'ra_validate:6' \
  --invoke-with-args 'ra_validate:7' \
  --invoke-with-args 'ra_validate:8' \
  --invoke-with-args 'ra_validate:9' \
  --invoke-with-args 'ra_validate:10' \
  --invoke-with-args 'ra_validate:11' \
  --invoke-with-args 'ra_validate:12' \
  --invoke-with-args 'ra_validate:13' \
  --invoke-with-args 'ra_validate:14' \
  --invoke-with-args 'ra_validate:15' \
  --invoke-with-args 'ra_validate:16' \
  --invoke-with-args 'ra_validate:17' \
  --invoke-with-args 'ra_validate:18' \
  --invoke-with-args 'ra_validate:19' \
  --invoke-with-args 'ra_validate:20' \
  --invoke-with-args 'ra_validate:21' \
  --invoke-with-args 'ra_validate:99' \
  `# riscv build_options bounds gate — mem == 0 || !mem.is_power_of_two()` \
  --invoke-with-args 'rv_bounds_gate:2,0' \
  --invoke-with-args 'rv_bounds_gate:2,65536' \
  --invoke-with-args 'rv_bounds_gate:2,196608' \
  --invoke-with-args 'rv_bounds_gate:2,1' \
  --invoke-with-args 'rv_bounds_gate:1,65536' \
  --invoke-with-args 'rv_bounds_gate:1,0' \
  --invoke-with-args 'rv_bounds_gate:0,0' \
  --invoke-with-args 'rv_bounds_gate:0,65536' \
  `# a non-RISC-V target: flips ensure_supported_target's conjunction` \
  --invoke-with-args 'rv_bounds_gate:3,65536' \
  --invoke-with-args 'rv_bounds_gate:3,0' \
  -o "$OUT/run.json"

"$WITNESS" report --input "$OUT/run.json" --format mcdc > "$OUT/report.txt"
"$WITNESS" report --input "$OUT/run.json" --format mcdc-json > "$OUT/report.json"
"$WITNESS" report --input "$OUT/run.json" --format mcdc-rollup > "$OUT/rollup.txt"

echo "wrote $OUT/report.txt $OUT/report.json $OUT/rollup.txt"
