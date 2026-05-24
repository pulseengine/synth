# Release Process

How synth cuts a release: cross-platform binaries, SHA256 checksums, SLSA
build provenance, and Sigstore keyless signatures. The pipeline lives in
`.github/workflows/release.yml` and is modelled on the sibling PulseEngine
release workflows (`pulseengine/witness`, `pulseengine/rivet`, and the
supply-chain reference `pulseengine/sigil`).

## TL;DR — cutting a release

```bash
# 1. land all changes on main, with a green CI run
# 2. bump the workspace version + update CHANGELOG (see checklist below)
# 3. tag and push
git tag -a v0.3.1 -m "synth v0.3.1"
git push origin v0.3.1
```

Pushing a `v*` tag triggers `release.yml`. No further manual steps are
required — the workflow builds the binaries, signs them, and publishes the
GitHub Release. If a run fails partway, re-run it from the Actions tab via
the `workflow_dispatch` trigger, passing the existing tag name.

## What the workflow does

Trigger: `push` of a tag matching `v*` (or manual `workflow_dispatch` with
an existing tag).

1. **`build-binaries`** — builds the `synth` CLI (`cargo build --release -p
   synth-cli`) for a host matrix:
   - `x86_64-unknown-linux-gnu`
   - `aarch64-unknown-linux-gnu` (via `cross`)
   - `x86_64-apple-darwin`
   - `aarch64-apple-darwin`

   Each target is stripped, packaged as `synth-<version>-<target>.tar.gz`
   (with `README.md` + `LICENSE`), and uploaded as a workflow artifact.

   The build uses only the `riscv` feature (the workspace default). The
   `verify` feature is **not** enabled — it pulls `z3-sys`, which vendors
   and compiles Z3 from source (slow, needs network, large C++ build). The
   CLI degrades gracefully: `synth verify` without the feature prints
   "rebuild with `--features verify`". This keeps the release build fast and
   free of the `libz3-dev` / temp-disk issues documented in `ci.yml`.

2. **`create-release`** — collects all archives, then:
   - Generates `SHA256SUMS.txt` over every archive.
   - Generates **SLSA build provenance** for every `.tar.gz` via
     `actions/attest-build-provenance` (GitHub-native attestation).
   - Signs `SHA256SUMS.txt` with **cosign keyless** (Sigstore), emitting
     `SHA256SUMS.txt.cosign.bundle`, `.sig`, and `.pem`.
   - Captures a `build-env.txt` (rustc / cargo / cosign / runner versions).
   - Creates (or updates, idempotently) the GitHub Release and attaches all
     assets.

## Provenance and signing model

synth uses **two complementary mechanisms**, matching the sibling repos:

### SLSA build provenance (GitHub-native)

`actions/attest-build-provenance` produces an in-toto SLSA v1 provenance
statement for every release binary archive. The attestation is signed
keyless via Sigstore (Fulcio mints a short-lived certificate bound to the
workflow's OIDC identity) and logged in the Rekor transparency log. GitHub
also stores it as a first-class attestation on the repo.

Consumer verification:

```bash
gh attestation verify synth-v0.3.1-x86_64-unknown-linux-gnu.tar.gz \
  --repo pulseengine/synth
```

This proves the archive was built by `release.yml` in `pulseengine/synth`,
from a specific commit, without anyone holding a long-lived signing key.

### Sigstore keyless signature on SHA256SUMS

`SHA256SUMS.txt` is signed with `cosign sign-blob` (keyless OIDC). This
closes the gap where an attacker able to replace a release asset could also
replace a plain, unsigned checksum file. The `.cosign.bundle` is the
self-contained verification artifact (no Rekor round-trip needed).

Consumer verification:

```bash
cosign verify-blob \
  --certificate-identity-regexp \
    'https://github.com/pulseengine/synth/.github/workflows/release.yml@.*' \
  --certificate-oidc-issuer \
    'https://token.actions.githubusercontent.com' \
  --bundle SHA256SUMS.txt.cosign.bundle \
  SHA256SUMS.txt

# then verify your downloaded binary against the trusted checksums
sha256sum --check --ignore-missing SHA256SUMS.txt
```

No long-lived keys exist anywhere: the trust anchor is the GitHub Actions
OIDC identity (workflow ref + repo + commit). There is nothing to rotate.

## Release checklist

Before pushing a `v*` tag:

- [ ] All target changes merged to `main`; CI green on the merge commit.
- [ ] `cargo test --workspace` passes locally.
- [ ] `cargo clippy --workspace --all-targets -- -D warnings` clean.
- [ ] `cargo fmt --check` clean.
- [ ] Version bumped in `Cargo.toml` (`[workspace.package] version`) — all
      crates inherit it via `version.workspace = true`.
- [ ] `Cargo.lock` updated (run `cargo build` after the bump, commit it).
- [ ] `CHANGELOG.md` updated (see mapping below).
- [ ] Tag name matches the `Cargo.toml` version exactly (`v0.3.1` ↔ `0.3.1`).

After the workflow finishes:

- [ ] GitHub Release page shows 4 `.tar.gz` archives + `SHA256SUMS.txt` +
      `SHA256SUMS.txt.{cosign.bundle,sig,pem}` + `build-env.txt`.
- [ ] Spot-check one binary: download, `gh attestation verify`, run
      `synth --version`.

## CHANGELOG.md mapping

synth keeps a [Keep a Changelog](https://keepachangelog.com/) file. The
`v0.3.x` series has per-version sections (`## [0.3.0] - <date>`, etc.).

When cutting `vX.Y.Z`:

1. Rename the existing `## [Unreleased]` section to
   `## [X.Y.Z] - YYYY-MM-DD`.
2. Add a fresh empty `## [Unreleased]` section above it.
3. Keep the `### Added` / `### Fixed` / `### Changed` subsection structure.

The workflow's GitHub Release body is auto-generated from commit history
(`gh release create --generate-notes`); the hand-curated `CHANGELOG.md`
section remains the canonical, human-readable record. The two are
complementary — do not drop the CHANGELOG.

## Build tooling decision: hand-rolled, not cargo-dist

None of the three sibling repos (`witness`, `rivet`, `sigil`) use
`cargo-dist`. They all hand-roll a build matrix with `dtolnay/rust-toolchain`
+ `cross` + `actions/upload-artifact`, and publish via `gh release`. synth
follows the same pattern for consistency across the org and to keep the
workflow auditable. If the org later standardises on `cargo-dist`, synth can
migrate — but adopting it unilaterally here would diverge from the siblings.

---

# Release Pipeline — Phased Plan

The maintainer asked for the rollout to be staged. The committed
`release.yml` already implements **Phases 1–3**; Phases 4–5 are future work.

## Phase 1 — Binaries + checksums + GitHub Release  ✅ implemented

- **Delivers:** cross-platform `synth` binaries (4 host targets) packaged as
  `.tar.gz`, a `SHA256SUMS.txt`, and an automated GitHub Release on tag push.
- **Effort:** ~0.5 day (done).
- **Depends on:** nothing. This is the foundation.

## Phase 2 — SLSA build provenance  ✅ implemented

- **Delivers:** an in-toto SLSA v1 provenance attestation per binary
  archive, via `actions/attest-build-provenance`, verifiable with
  `gh attestation verify`.
- **Effort:** ~0.25 day (done) — one workflow step + the `attestations:
  write` and `id-token: write` permissions.
- **Depends on:** Phase 1.

## Phase 3 — cosign / Sigstore keyless signing  ✅ implemented

- **Delivers:** a Sigstore keyless signature over `SHA256SUMS.txt`
  (`.cosign.bundle` + `.sig` + `.pem`), verifiable with `cosign
  verify-blob`. Trust anchored to the workflow's OIDC identity.
- **Effort:** ~0.25 day (done) — `sigstore/cosign-installer` + one
  `sign-blob` step.
- **Depends on:** Phases 1–2 and the `id-token: write` permission.

## Phase 4 — crates.io publishing  ⬜ future

- **Delivers:** `cargo publish` of the workspace crates on tag push, so
  `cargo install synth-cli` works.
- **Effort:** ~0.5–1 day. The 17-crate workspace must be published in
  dependency order; `sigil` solves this with a `scripts/publish.rs` helper —
  synth would mirror that, or use a publish-ordering tool.
- **Depends on:** a `CRATES_IO_TOKEN` secret (or crates.io **trusted
  publishing** via OIDC, which `sigil` uses and is preferred — no token to
  store). All crate metadata (`description`, `license`, `repository`) must be
  complete and every dependency must be a published version, not a `path`.
- **Decision needed:** confirm whether synth crates should go to crates.io
  at all; if yes, set up trusted publishing on crates.io for the repo.

## Phase 5 — signing synth's *output* ELF binaries  ✅ compiler-side implemented

- **Delivers:** `synth compile --sign-output` invokes sigil's `wsc sign
  --keyless --format elf` after writing the ELF, attaching a Sigstore
  keyless signature in place. Off by default — opt in per-invocation; the
  unsigned compile path is unchanged for consumers without `wsc` installed.
  See [`sigil-integration.md`](sigil-integration.md) for the full design,
  trust model, verification command, and the wsc-contract assumption.
- **Status:** compiler-side wired (`crates/synth-cli/src/sign.rs`); the
  signing subprocess shape, missing-wsc error path, and `--all-exports`
  interaction are unit-tested. End-to-end signing + verification against a
  live `wsc` binary was deferred to the maintainer (the implementing agent
  did not have `wsc` on PATH).
- **Pipeline integration is out of scope here** — wiring `--sign-output`
  into `release.yml` (and uploading signed firmware as a release asset) is
  the natural follow-up alongside Phase 6's `--sbom` plumbing.

## Phase 6 — CycloneDX SBOM auto-emit  ⬜ future

- **Delivers:** the release workflow passes `--sbom` whenever it exercises
  synth, so every published firmware artifact ships a CycloneDX 1.5 SBOM
  (`.cdx.json`) as a release asset, signed alongside the binaries.
- **Already implemented in the compiler:** `synth compile --sbom` emits the
  SBOM today — see [`docs/sbom.md`](sbom.md). The SBOM documents the synth
  compiler, the input WASM, the output ELF (hashes + sizes), and the WASM
  module's imports, and is the artifact consumed by `rivet import --format
  cyclonedx` for rivet #107's `sbom-record`.
- **Remaining work:** wire `--sbom` into `release.yml` and upload the
  `.cdx.json` as a release asset. **Not done here** — the compiler-side
  capability is complete; only the CI plumbing is outstanding.
- **Depends on:** Phase 1.
