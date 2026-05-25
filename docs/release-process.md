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
   - Generates a CycloneDX 1.5 JSON SBOM for the synth toolchain via
     `cargo cyclonedx` (Phase 6) and writes it to
     `release-assets/synth-<VERSION>.cdx.json`.
   - Generates `SHA256SUMS.txt` over every archive *and* the SBOM.
   - Generates **SLSA build provenance** for every `.tar.gz` via
     `actions/attest-build-provenance` (GitHub-native attestation).
   - Signs `SHA256SUMS.txt` with **cosign keyless** (Sigstore), emitting
     `SHA256SUMS.txt.cosign.bundle`, `.sig`, and `.pem`. The signature
     transitively covers the SBOM (its digest is in SHA256SUMS.txt).
   - Captures a `build-env.txt` (rustc / cargo / cosign / runner versions).
   - Creates (or updates, idempotently) the GitHub Release and attaches all
     assets.

3. **`publish-to-crates-io.yml`** (parallel workflow, same `v*` trigger)
   — see Phase 4 below. Pushes the publishable workspace crates to
   crates.io via OIDC trusted publishing.

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
      `SHA256SUMS.txt.{cosign.bundle,sig,pem}` + `build-env.txt` +
      `synth-<VERSION>.cdx.json` (toolchain SBOM, Phase 6).
- [ ] Spot-check one binary: download, `gh attestation verify`, run
      `synth --version`.
- [ ] `publish-to-crates-io.yml` ran green: confirm
      `cargo install synth-cli` works on a clean machine, or check
      <https://crates.io/crates/synth-cli> shows the new version.

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

## Phase 4 — crates.io publishing  ✅ implemented

- **Delivers:** the workspace's publishable crates are pushed to crates.io
  on every `v*` tag, in parallel with `release.yml`. The workflow is
  `.github/workflows/publish-to-crates-io.yml`; the dependency-order walk
  is in `scripts/publish.rs` (compiled at workflow start by `rustc`).
  Final user-visible result: `cargo install synth-cli` works after the
  first release that runs this pipeline.
- **Trust model:** an org-wide `CRATES_IO_TOKEN` secret on the
  `pulseengine` GitHub organization, inherited by this repo. The
  workflow exports it as `CARGO_REGISTRY_TOKEN` for `./publish verify`
  and `./publish publish`. Migration to OIDC trusted publishing (to
  match sigil) is tracked as future work — see "Phase 4 — auth model"
  below; we chose the token path first because the org secret already
  exists and OIDC requires per-crate trusted-publisher registration
  (11 forms) before any publish succeeds.
- **Versioning convention.** Trusted publishing requires a real semver, so
  the workspace `version` is now bumped pre-tag in lockstep with the
  release tag (e.g. `v0.6.0` ⇔ `version = "0.6.0"`). The publish workflow
  verifies the tag matches the `[workspace.package]` version and refuses
  to run otherwise.
- **Published crate set (curated, conservative — leans toward
  *less* publishing).** Internal-only crates are marked
  `publish = false` and never reach crates.io.

  | Crate                  | Published? | Notes |
  | ---------------------- | ---------- | ----- |
  | `synth-cli`            | yes        | the public CLI |
  | `synth-core`           | yes        | dep of CLI |
  | `synth-frontend`       | yes        | dep of CLI |
  | `synth-synthesis`      | yes        | dep of CLI |
  | `synth-backend`        | yes        | dep of CLI |
  | `synth-backend-awsm`   | yes        | optional dep of CLI |
  | `synth-backend-wasker` | yes        | optional dep of CLI |
  | `synth-backend-riscv`  | yes        | default optional dep of CLI |
  | `synth-cfg`            | yes        | transitive dep |
  | `synth-opt`            | yes        | transitive dep |
  | `synth-verify`         | yes        | optional `verify` feature |
  | `synth-analysis`       | no         | not on the public face |
  | `synth-abi`            | no         | not on the public face |
  | `synth-memory`         | no         | not on the public face |
  | `synth-qemu`           | no         | dev/test only |
  | `synth-test`           | no         | dev/test binary |
  | `synth-wit`            | no         | not on the public face |

  Crates marked `publish = false` can be promoted later; promotion only
  requires removing the line, adding `description`/`license` if not
  inherited, and updating `scripts/publish.rs` so the order is right.
- **Internal path deps.** Every published crate's internal deps now carry
  both `path` and `version` (e.g. `synth-core = { path = "../synth-core",
  version = "0.6.0" }`). cargo uses `path` for in-workspace builds and
  rewrites to `version` on publish; both must be kept in lockstep with the
  workspace version bump.

### Phase 4 — auth model

The current workflow uses an **org-wide `CRATES_IO_TOKEN`** secret
inherited from `pulseengine`. No per-crate registration is required.
The token's scope (which crates it can publish) is determined by the
crates.io account that issued it; for fresh crate names the token's
owner must have the right to claim them.

**First-time publishes** still need a one-time manual step per crate
to claim each name on crates.io (crates.io rejects automated publishes
of crate names that have never existed). After the manual claim, every
subsequent `v*` tag publishes that crate automatically.

For each crate in the "Published? yes" table above that has never been
published:

```bash
# Get the token from `pulseengine` org settings or your crates.io account
export CARGO_REGISTRY_TOKEN=<token>
cargo publish -p <crate>   # in dependency order — see scripts/publish.rs
```

After this one-time claim, the automated workflow takes over on every
`v*` tag.

**Future work — migrate to OIDC trusted publishing.** Matching sigil's
pattern is the long-term plan (short-lived tokens, no stored secret),
but requires per-crate trusted-publisher registration on crates.io
(11 forms). Tracked as a follow-up; not blocking v0.6.x / v0.7.x.

## Phase 5 — signing synth's *output* ELF binaries  ✅ compiler-side implemented + CI-validated end-to-end

- **Delivers:** `synth compile --sign-output` invokes sigil's `wsc sign
  --keyless --format elf` after writing the ELF, attaching a Sigstore
  keyless signature in place. Off by default — opt in per-invocation; the
  unsigned compile path is unchanged for consumers without `wsc` installed.
  See [`sigil-integration.md`](sigil-integration.md) for the full design,
  trust model, verification command, and the wsc-contract assumption.
- **Status:** compiler-side wired (`crates/synth-cli/src/sign.rs`); the
  signing subprocess shape, missing-wsc error path, and `--all-exports`
  interaction are unit-tested. End-to-end against a real `wsc` binary is
  CI-validated via `.github/workflows/signing-e2e.yml` +
  `tests/wsc_sign_e2e.sh`:
  - The workflow downloads a sha256-pinned `wsc` (currently
    `pulseengine/sigil` `v0.9.0`) and runs the e2e script on every PR
    that touches `crates/synth-cli/src/sign.rs`, `main.rs`, or the test
    itself, plus on every `v*` tag push.
  - Three cases are checked: (a) WASM keyless sign+verify round-trip,
    (b) synth's actual `--sign-output` invocation against ELF, and
    (c) a tamper-negative on the case-(a) signed WASM. Case (b)
    currently pins the **known sigil-v0.9.0 ELF-keyless gap** (sigil
    rejects keyless ELF with an explicit usage error); the test
    asserts the gap and emits a GitHub `::notice::` annotation if
    sigil ever lifts it, alerting us to promote the test to a real
    "signed ELF" assertion.
- **Pipeline integration is out of scope here** — wiring `--sign-output`
  into `release.yml` (and uploading signed firmware as a release asset) is
  blocked on sigil shipping keyless-ELF support. Once the e2e job starts
  producing a real signed ELF (case (b) flips to positive), the release
  workflow can add a signing step alongside Phase 6's SBOM emission.

## Phase 6 — CycloneDX SBOM auto-emit  ✅ implemented

- **Delivers:** the release workflow emits a CycloneDX 1.5 JSON SBOM for
  the **synth toolchain itself** and attaches it to the GitHub Release.
  Asset name: `synth-v<VERSION>.cdx.json` (e.g. `synth-v0.6.0.cdx.json`).
  The SBOM is produced by `cargo cyclonedx --format json --spec-version
  1.5 -p synth-cli` and covers every Rust dependency that goes into the
  released `synth` binary.
- **Two distinct SBOMs.** Do not conflate them — see [`docs/sbom.md`](sbom.md)
  for the full distinction.
  - The **toolchain SBOM** added in Phase 6 (this section) is shipped
    *with the release* and documents what synth itself is built from.
  - The **per-compilation SBOM** emitted by `synth compile --sbom` (added
    in #129) is produced *by* synth at use time and documents one
    compilation transaction (compiler + input WASM + output ELF + WASM
    imports).
- **Signing.** The toolchain SBOM is written into `release-assets/`
  *before* the SHA256SUMS step, so its digest is captured in the
  signed checksum manifest. The cosign keyless signature over
  `SHA256SUMS.txt` (Phase 3) transitively covers the SBOM — no
  separate signing step is needed.
- **Depends on:** Phase 1 (Release-asset upload path; the new step
  reuses `release-assets/` and the existing `gh release upload`).
