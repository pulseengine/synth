# Sigil integration — signing synth's output ELF binaries

This is the implementation of [Phase 5 of the release roadmap](release-process.md#phase-5--signing-synths-output-elf-binaries--future):
synth invokes [sigil](https://github.com/pulseengine/sigil)'s `wsc` CLI to
attach a Sigstore keyless signature to the ARM / RISC-V ELF binaries `synth
compile` produces.

The compiler-side toggle is `synth compile --sign-output`. It is **off by
default** — signing requires the external `wsc` binary, network access to
Sigstore (Fulcio + Rekor), and a few seconds of latency. The unsigned compile
path is unchanged for consumers who do not have `wsc` installed.

## What this proves

The signature embedded in the ELF lets a downstream consumer verify, without
any pre-shared key, that:

1. **The ELF was produced by a specific identity.** A Fulcio short-lived
   certificate (~10 minutes) binds the signature to the OIDC subject that
   requested it — e.g. `https://github.com/pulseengine/synth/.github/workflows/release.yml@refs/tags/v0.6.0`
   for a release-pipeline run.
2. **The signature was logged in Rekor at time T.** Rekor's transparency
   log gives the consumer a tamper-evident witness of *when* this ELF was
   signed, independent of clock skew at the verifier.
3. **The unsigned bytes hash to the value the signature covers.** Standard
   Sigstore semantics.

What it does *not* prove on its own:

- It does not prove the WASM input was unmodified — that is what the
  `--sbom` flag's CycloneDX SBOM is for (it records the input WASM hash;
  see [`sbom.md`](sbom.md)). The two flags compose: see
  [SBOM interaction](#interaction-with---sbom) below.
- It does not prove correctness of compilation — that is what the Rocq
  proofs (`coq/Synth/`) cover for the operations they reach.

## Dependency: `wsc` on PATH

`wsc` ships from [sigil's `wsc-cli` crate](https://github.com/pulseengine/sigil/tree/main/src/cli).
Both `wsc` and `sigil` binaries point at the same entry point; synth shells
out to `wsc` (the canonical PulseEngine name).

Install options:

- **From source** (current method):
  ```bash
  cargo install --git https://github.com/pulseengine/sigil --bin wsc
  ```
- **From crates.io** once sigil publishes (tracked in sigil's release plan).
- **In CI**: a GitHub Action analogous to `sigstore/cosign-installer` is
  planned by sigil; until then, build from source in the workflow.

When the binary is missing, `synth compile --sign-output` exits with a clear
actionable error pointing at sigil's install instructions; the ELF is still
written to disk, so a user who wants to retry signing later can do so by
running `wsc sign` directly.

## Usage

```bash
# Sign the compiled ELF in place. Requires `wsc` on PATH plus an OIDC token
# in the environment (e.g. GitHub Actions with `id-token: write`).
synth compile input.wat --cortex-m -o firmware.elf --sign-output

# Compose with --all-exports: the multi-function ELF is signed once.
synth compile module.wasm --all-exports --cortex-m -o fw.elf --sign-output

# Compose with --sbom: SBOM records the unsigned ELF hash; on-disk ELF
# after this command is the signed version. See "Interaction with --sbom".
synth compile input.wat --cortex-m -o fw.elf --sbom --sign-output
```

On success synth prints `signed: <path>` to stdout and exits 0. On failure
(wsc missing, OIDC token missing, Fulcio outage, Rekor outage, etc.) synth
exits non-zero with the wsc stderr captured in the error message.

### Verification (consumer side)

```bash
wsc verify --keyless --format elf \
  --cert-identity "https://github.com/pulseengine/synth/.github/workflows/release.yml@refs/tags/v0.6.0" \
  --cert-oidc-issuer "https://token.actions.githubusercontent.com" \
  -i firmware.elf
```

The exact `--cert-identity` regex depends on how the firmware was signed
(local developer signs with their own GitHub identity; CI signs with the
workflow identity). Producers should publish the expected identity alongside
the firmware. See [sigil's `docs/keyless.md`](https://github.com/pulseengine/sigil/blob/main/docs/keyless.md)
for the full verification surface.

## Interaction with `--sbom`

When both flags are supplied:

1. synth writes the unsigned ELF to disk.
2. synth emits the CycloneDX SBOM — it records the hash of the **unsigned**
   synth output (the bytes synth actually produced, not the post-signing
   bytes).
3. synth invokes `wsc sign` — the on-disk ELF is replaced with the signed
   version.

Net effect: a downstream consumer who receives both `firmware.elf` (signed)
and `firmware.elf.cdx.json` will see the SBOM hash differ from the on-disk
ELF hash. This is intentional — the SBOM is a record of synth's compilation
output, and the signature is an attestation over a transformed (signed) ELF.
If a downstream chain (rivet, etc.) needs both attestations to chain
cleanly, they should record the post-signing hash separately, or sign the
SBOM itself with `wsc sign --format wasm` once sigil supports JSON.

## Implementation

The signing path lives in [`crates/synth-cli/src/sign.rs`](../crates/synth-cli/src/sign.rs).
The exact subprocess invocation is:

```
wsc sign --keyless --format elf -i <output.elf> -o <output.elf>.signing.tmp
```

followed by an atomic `rename` of the `.signing.tmp` over the original. The
in-place semantics ("the path I passed to `-o` is the signed ELF") are
synth-side; wsc itself writes a fresh output file.

If wsc fails, the `.signing.tmp` is removed; the original unsigned ELF
remains on disk so the user can re-attempt or hand-sign.

### The wsc contract synth assumes

As of `wsc-cli` v0.9.x (sigil `main` branch, October 2025) `wsc sign`
accepts:

| Flag | Meaning |
|------|---------|
| `--keyless` | Sigstore ephemeral keys + Fulcio cert + Rekor log entry. |
| `--format elf` | ELF signing format (signature embedded in a dedicated section). |
| `-i <path>` | Input file. |
| `-o <path>` | Output file (wsc writes here; does not modify input in place). |

If a future wsc release changes this surface (e.g. renames `sign --format
elf` to `sign-elf`, or drops `--keyless` in favor of `--mode keyless`),
synth's signing subprocess will fail with a non-zero exit and the wsc
stderr will be surfaced verbatim. The error message includes a "sigil
interface assumption broken — update `crates/synth-cli/src/sign.rs`" hint
so the failure mode is loud, not silent.

## Trust model

The trust chain for a synth-produced, sigil-signed ELF:

```
GitHub Actions OIDC token  ──→  Fulcio short-lived cert  ──→  Ed25519 signature
       (identity claim)              (binds cert ←→ identity)        (over ELF hash)
                                                                            │
                                                                            ▼
                                                                   Rekor log entry
                                                                   (witness of time T)
```

A consumer who has:

- The published `--cert-identity` regex (or exact value) for the release
  workflow they trust.
- The `--cert-oidc-issuer` URL (always `https://token.actions.githubusercontent.com`
  for GitHub).
- Network access to Rekor (`rekor.sigstore.dev`).

…can run `wsc verify --keyless` and end with cryptographic evidence that
*"this ELF was produced by user@org via the synth compiler at time T"*. No
long-lived signing key needs to be managed.

## Status

Implemented in `feat/sigil-elf-signing`. Validated:

- Unit tests pin the `wsc` argv shape and the missing-wsc error path
  (`crates/synth-cli/src/sign.rs::tests`).
- Manual smoke test of `synth compile --demo add --sign-output` (without
  wsc installed) confirms exit code 1 with the actionable error.
- End-to-end signing + verification **was not validated by the implementing
  agent** — `wsc` was not available in that environment. A maintainer with
  `wsc` installed should run the verification command above against an ELF
  signed locally to confirm the wsc contract assumption.

## Out of scope

- **Pipeline integration** (Phase 6 territory): wiring `--sign-output` into
  `release.yml` so every published firmware artifact ships signed.
- **Bulk signing of release assets**: at release time the workflow may also
  want to sign the source SBOM, the SHA256SUMS, and other release assets
  — Phase 3 already handles `SHA256SUMS.txt` via cosign keyless.
- **Detached signatures**: synth always asks for an embedded signature
  (`wsc sign` without `--signature-file`). If a consumer wants a detached
  `.sig` they can re-sign separately via `wsc sign -S <path>`.
