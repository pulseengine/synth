#!/usr/bin/env bash
# #1000 (RQ-58-SHIPVERIFY) — released-artifact non-vacuity gate for `synth verify`.
#
# `synth verify` existed in the tree and in --help for many releases while NO
# obtainable artifact carried the `verify` feature (confirmed on 0.55.0 and
# 0.57.0 — every platform tarball failed with the capability error). This
# script is the gate that keeps "we ship the feature" from silently regressing
# back to "we ship the help text": it takes a synth BINARY (in release.yml, the
# one extracted from the just-packaged tarball — the artifact itself, not a dev
# build), compiles a module with it, runs `synth verify` on that module, and
# asserts a REAL verdict:
#
#   * exit 0,
#   * the human verdict line ("All functions verified successfully."),
#   * a machine-readable report (--emit-verify-report) whose summary proves
#     >= 1 rule kind was actually verified and 0 failed,
#   * and the absence of the capability-missing error.
#
# RED DIRECTION (what makes this gate non-vacuous): against a binary built
# WITHOUT `--features verify` the verify step exits 1 with "built without the
# `verify` feature" and this script FAILS. The fact-spec-oracle CI job runs
# that red leg on every push (build without the feature, assert this script
# fails for exactly that reason), so the gate's ability to go red is itself
# CI-pinned — this repo has shipped gates that could not fail.
#
# Usage:
#   scripts/release_verify_smoke.sh <path-to-synth-binary>
#
# Env:
#   SYNTH_RUNNER — optional command prefix used to execute the binary, for
#     tarballs the host cannot run natively (release.yml sets
#     `qemu-aarch64 -L /usr/aarch64-linux-gnu` for the aarch64-linux tarball).
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: $0 <path-to-synth-binary>" >&2
  exit 2
fi
SYNTH=$1
test -x "$SYNTH" || { echo "error: '$SYNTH' is not an executable file" >&2; exit 2; }

# Intentionally unquoted: SYNTH_RUNNER is a command PREFIX and must word-split
# (bash word-splits unquoted expansions; this script is bash via its shebang).
RUNNER=${SYNTH_RUNNER:-}
run_synth() {
  # shellcheck disable=SC2086
  $RUNNER "$SYNTH" "$@"
}

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# Same fixture shape as tests/verify_banner_1000.rs: exported function whose
# ops (and/add) are on the verified ARM rule path.
cat > "$TMP/mix.wat" <<'EOF'
(module
  (func (export "mix") (param i32 i32) (result i32)
    local.get 0
    i32.const 255
    i32.and
    local.get 1
    i32.add))
EOF

echo "== release_verify_smoke: $SYNTH ${RUNNER:+(runner: $RUNNER)}"
run_synth --version

# 1. The artifact must be able to COMPILE the module it is about to verify.
#    No pipes anywhere below: `cmd | tail` has produced false PASSes in this
#    repo twice — capture to a file, check rc, then read the file.
if ! run_synth compile "$TMP/mix.wat" -o "$TMP/mix.elf" --all-exports \
    > "$TMP/compile.log" 2>&1; then
  echo "FAIL: synth compile failed" >&2
  cat "$TMP/compile.log" >&2
  exit 1
fi

# 2. The verdict, not the help text: `synth verify` must run to a verdict.
if ! run_synth verify "$TMP/mix.wat" "$TMP/mix.elf" \
    --emit-verify-report "$TMP/report.json" \
    > "$TMP/verify.log" 2>&1; then
  echo "FAIL: synth verify exited non-zero — this artifact cannot verify" >&2
  cat "$TMP/verify.log" >&2
  exit 1
fi

if grep -q 'built without the `verify` feature' "$TMP/verify.log"; then
  echo "FAIL: capability-missing error in a run that exited 0 (should be unreachable)" >&2
  cat "$TMP/verify.log" >&2
  exit 1
fi

if ! grep -q 'All functions verified successfully\.' "$TMP/verify.log"; then
  echo "FAIL: no verification verdict in output" >&2
  cat "$TMP/verify.log" >&2
  exit 1
fi

# 3. Machine-readable verdict: the synth-verify-v1 summary must show real
#    verified rule kinds and zero failures — a grep for a sentence can rot,
#    counts cannot.
if ! python3 - "$TMP/report.json" <<'PY'
import json, sys
with open(sys.argv[1]) as f:
    report = json.load(f)
assert report.get("schema") == "synth-verify-v1", f"unexpected schema: {report.get('schema')}"
s = report["summary"]
assert s["verified"] >= 1, f"no rule kind was actually verified: {s}"
assert s["failed"] == 0, f"verification failures in the smoke fixture: {s}"
print(f"verdict: {s['verified']} verified / {s['failed']} failed / "
      f"{s['unknown']} unknown / {s['declined']} declined "
      f"across {s['applied_rule_kinds']} applied rule kinds")
PY
then
  echo "FAIL: verify report did not carry a real verdict" >&2
  cat "$TMP/verify.log" >&2
  exit 1
fi

echo "PASS: released artifact runs 'synth verify' to a real verdict"
