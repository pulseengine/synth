# Synth Project Status — moved

This file used to restate project status by hand and was pinned by nothing —
by the time of the #946 doc sweep it was ~16 months stale (it said 291 Qed
while the tree held 592, 16 crates while the workspace held 18, named Z3 as
the default validator three eras after ordeal replaced it, and listed
multi-memory and bulk memory as missing after both had shipped and been
claim-pinned). Restating status in a second place is how status goes stale,
so the restatement is deleted rather than re-synced.

Current status lives in the sources of truth:

- **[`docs/status/FEATURE_MATRIX.md`](FEATURE_MATRIX.md)** — the generated
  op-surface and capability matrix (rendered from
  `scripts/templates/feature_matrix.md.tmpl` by
  `python3 scripts/claim_check.py claims.yaml --emit-status`; staleness-gated
  in CI).
- **`artifacts/status.json`** — the machine-derived numbers (proof counts,
  rule counts, harness counts; re-derived on every commit by the claim gate).
- **[`coq/STATUS.md`](../../coq/STATUS.md)** — Rocq proof coverage, per-file
  breakdown, tiers, and the trusted base.
- **`artifacts/verified-codegen-roadmap.yaml`** — VCR-* roadmap statuses
  (single source for roadmap claims).
- **[`README.md`](../../README.md)** — the prose overview, whose load-bearing
  claims are pinned in `claims.yaml` and re-derived by
  `scripts/claim_check.py` in CI.
