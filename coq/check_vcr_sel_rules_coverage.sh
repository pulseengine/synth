#!/usr/bin/env bash
# VCR-SEL-001 (#242) coverage gate: every rule in the DSL table must carry its
# Qed'd Rocq theorem — a rule without a theorem cannot merge.
#
# Reads coq/vcr_sel_rules.manifest (one rule name per line; pinned 1:1 to the
# Rust table crates/synth-synthesis/src/sel_dsl/mod.rs RULES by the cargo test
# sel_dsl::tests::manifest_matches_rule_table) and checks that
# coq/Synth/Synth/VcrSelRules.v has, per rule:
#   - `Definition <rule>`          (the lowering the theorem is about), and
#   - `Theorem <rule>_correct`     (the 1:1-named T1 obligation);
# and that the file contains NO `Admitted`/`admit.` — combined with the file
# compiling under //coq:verify_proofs, that means every theorem is Qed.
#
# Part of the //coq:verify_proofs test_suite, so CI's
# `bazel test //coq:verify_proofs` fails when coverage is broken.
set -euo pipefail

v_file="$1"
manifest="$2"

fail=0
rules=0

while IFS= read -r rule; do
  # Skip blanks and comments.
  rule="${rule%%#*}"
  rule="$(echo "${rule}" | tr -d '[:space:]')"
  [ -z "${rule}" ] && continue
  rules=$((rules + 1))
  if ! grep -q "Definition ${rule} " "${v_file}"; then
    echo "ERROR: rule '${rule}' has no 'Definition ${rule}' in ${v_file}" >&2
    fail=1
  fi
  if ! grep -q "Theorem ${rule}_correct " "${v_file}"; then
    echo "ERROR: rule '${rule}' lacks its theorem '${rule}_correct' in ${v_file}" >&2
    fail=1
  fi
done < "${manifest}"

if [ "${rules}" -eq 0 ]; then
  echo "ERROR: no rules found in ${manifest} — the manifest must list every DSL rule" >&2
  fail=1
fi

if grep -nE 'Admitted|admit\.' "${v_file}"; then
  echo "ERROR: ${v_file} contains Admitted/admit — every rule theorem must be Qed" >&2
  fail=1
fi

if [ "${fail}" -ne 0 ]; then
  exit 1
fi

echo "OK: ${rules} rules, each with a Definition and a 1:1 theorem, no Admitted."
