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
- **Trust model:** crates.io **trusted publishing** via GitHub OIDC.
  No `CRATES_IO_TOKEN` is stored on the repo;
  `rust-lang/crates-io-auth-action@v1` exchanges the workflow's OIDC token
  for a short-lived crates.io token scoped to the listed crates. There is
  nothing to rotate.
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

### Phase 4 — user-side setup (required before the first publish)

Trusted publishing requires a per-crate registration on crates.io.
Until those are registered, the workflow will fail at the
`rust-lang/crates-io-auth-action` step (or, for crates that *do* have
trusted publishing but new ones don't, partway through `./publish
publish`). This step **cannot be automated** — it requires the
crates.io account that owns the crate (or, for first publishes, the
account that will own it) to manually configure trusted publishing.

For each crate in the "Published? yes" table above:

1. Sign in to <https://crates.io> with the account that will own the crate.
2. For a crate that does not yet exist, do a one-time manual
   `cargo publish` from a local trusted-publishing-compatible setup
   (or use the legacy token-based publish for the first version), so
   crates.io has a record to attach the trusted publisher to.
3. Navigate to <https://crates.io/crates/CRATENAME/settings> →
   *Trusted Publishing*. Click **Add GitHub Publisher** with:
   - Repository owner: `pulseengine`
   - Repository name: `synth`
   - Workflow filename: `publish-to-crates-io.yml`
   - Environment: *(leave empty)*
4. Repeat for every crate in the publishable set.

After registration, the next `v*` tag push triggers an end-to-end
publish without a stored token. Until registration is complete, the
workflow may need to be re-run from the Actions tab via
`workflow_dispatch` after each crate is registered.

## Phase 5 — signing synth's *output* ELF binaries  ⬜ future

- **Delivers:** synth invokes `sigil` to sign the ARM/RISC-V ELF binaries it
  *produces* (not the compiler itself). This is the natural PulseEngine
  integration: synth compiles, `sigil` attests the firmware artifact.
- **Effort:** unknown — a design spike is needed first. `sigil` already has
  an ELF signing format (`sigil sign --format elf --keyless`); the work is
  wiring a `synth compile --sign` path and deciding the trust model for
  embedded firmware.
- **Depends on:** Phases 1–4 and a separate design doc. **Out of scope for
  the current release-pipeline work** — noted here only as the intended
  future direction.

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
