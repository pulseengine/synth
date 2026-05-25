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

> **Status note (sigil v0.9.0, May 2026).** `wsc sign --keyless --format
> elf` is currently rejected by sigil with the literal error string
> *"Keyless signing is currently supported only for WASM format. Use
> key-based signing for ELF and MCUboot artifacts."* See
> [`src/cli/main.rs`](https://github.com/pulseengine/sigil/blob/v0.9.0/src/cli/main.rs#L770-L779).
> Until sigil ships keyless ELF support, `synth compile --sign-output`
> exits non-zero with the wsc rejection surfaced verbatim. The CI test
> (`tests/wsc_sign_e2e.sh`, workflow `signing-e2e.yml`) asserts exactly
> that current behaviour AND auto-detects when the situation flips,
> alerting maintainers via a `::notice::` GitHub annotation. The
> command below documents the *intended* verification UX once sigil
> ships ELF keyless; today the round-trip is only achievable for WASM
> modules (see [Verifying a signed WASM module locally](#verifying-a-signed-wasm-module-locally)
> below).

```bash
wsc verify --keyless --format elf \
  --cert-identity "https://github.com/pulseengine/synth/.github/workflows/release.yml@refs/tags/v0.6.0" \
  --cert-oidc-issuer "https://token.actions.githubusercontent.com" \
  -i firmware.elf
```

The exact `--cert-identity` value depends on how the firmware was signed
(local developer signs with their own GitHub identity; CI signs with the
workflow identity). Producers should publish the expected identity alongside
the firmware. Sigil's `wsc verify --keyless` accepts the literal
`--cert-identity` (string match) and `--cert-oidc-issuer` flags; there is
**no** `--cert-identity-regexp` flag in sigil v0.9.0 (see sigil's
[`src/cli/main.rs` lines 247-258](https://github.com/pulseengine/sigil/blob/v0.9.0/src/cli/main.rs#L247-L258)).
See [sigil's `docs/keyless.md`](https://github.com/pulseengine/sigil/blob/main/docs/keyless.md)
for the full verification surface.

### Verifying a signed WASM module locally

This is the path that actually works today. It is what `tests/wsc_sign_e2e.sh`
case 1 exercises in CI on every PR that touches the signing contract.

```bash
# 1. Build a WASM module (synth's WAT fixtures work, or any wasmparser-valid
#    module). For a developer-identity signature, install wsc from sigil:
cargo install --git https://github.com/pulseengine/sigil --bin wsc
wat2wasm tests/integration/add.wat -o /tmp/add.wasm

# 2. Sign with your developer GitHub identity (wsc opens an OIDC browser flow
#    for keyless signing outside CI).
wsc sign --keyless --format wasm -i /tmp/add.wasm -o /tmp/add.signed.wasm

# 3. Verify. With --cert-identity bound to your GitHub identity:
wsc verify --keyless --format wasm \
  --cert-identity 'you@example.com' \
  --cert-oidc-issuer 'https://github.com/login/oauth' \
  -i /tmp/add.signed.wasm

# Or, in a GitHub Actions workflow with id-token: write, the certificate
# identity is the workflow ref:
wsc verify --keyless --format wasm \
  --cert-identity 'https://github.com/pulseengine/synth/.github/workflows/signing-e2e.yml@refs/heads/main' \
  --cert-oidc-issuer 'https://token.actions.githubusercontent.com' \
  -i /tmp/add.signed.wasm
```

Omitting `--cert-identity` makes verify accept any identity that's anchored
in Rekor — useful for a quick health check but **insufficient for trust**
in production. Always pin the expected identity in any consumer-side script.

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

Implemented in `feat/sigil-elf-signing` (PR #135). End-to-end validation
landed in `feat/wsc-ci-end-to-end` via the `signing-e2e.yml` workflow.

Validated:

- Unit tests pin the `wsc` argv shape and the missing-wsc error path
  (`crates/synth-cli/src/sign.rs::tests`).
- Manual smoke test of `synth compile --demo add --sign-output` (without
  wsc installed) confirms exit code 1 with the actionable error.
- **End-to-end CI validation**: `.github/workflows/signing-e2e.yml`
  downloads a sha256-pinned `wsc` from sigil's releases (currently
  `v0.9.0`) and runs `tests/wsc_sign_e2e.sh`, which exercises three
  load-bearing cases:
  1. **WASM keyless sign + verify round-trip** — proves wsc is healthy,
     Fulcio + Rekor are reachable, the OIDC token works, and the keyless
     code path that sigil currently supports does sign and re-verify a
     module end-to-end.
  2. **Synth's actual ELF contract** — runs `synth compile --sign-output`
     and asserts the current sigil-v0.9.0 behaviour: wsc rejects keyless
     ELF with *"Keyless signing is currently supported only for WASM
     format"*; synth surfaces that error verbatim; the unsigned ELF
     stays untouched on disk; no stale `.signing.tmp` is left behind.
     The test also emits a GitHub `::notice::` annotation when sigil
     eventually lifts the ELF restriction, alerting maintainers to
     update the test (and ship a proper signed ELF in the release
     workflow).
  3. **Tamper-negative** (currently xfail — sigil#135) — flips a byte
     in the case-1 signed WASM and asserts `wsc verify --keyless`
     rejects it. **The CI run on commit 7f1a9c9 surfaced that
     wsc v0.9.0 accepts the tampered file (exit 0)** — verification
     is not detecting modifications inside the signed payload (offset
     64 in a 15 218-byte signed module, well before the trailing
     signature section). Filed upstream as
     [pulseengine/sigil#135](https://github.com/pulseengine/sigil/issues/135).
     The test is intentionally `xfail` against current wsc and will
     auto-`xpass`-notify when sigil#135 ships a fix; the assertion
     should then flip back to a hard rejection check. Until then,
     `wsc verify --keyless` should be treated as proving signature-blob
     well-formedness, **not** module integrity.

### Known contract gap (sigil v0.9.0)

Keyless ELF signing **does not work end-to-end** today, by sigil's design:
`wsc sign --keyless --format elf` returns an explicit usage error
(sigil's [`src/cli/main.rs:770-779`](https://github.com/pulseengine/sigil/blob/v0.9.0/src/cli/main.rs#L770-L779)).
synth-cli's `sign_elf` invokes exactly that argv shape, so `synth compile
--sign-output` currently always fails when a real `wsc` is on PATH.

This is a planned, tracked situation, not a bug in synth: synth-cli's
implementation is forward-compatible with the keyless-ELF support sigil
intends to add (the argv shape matches sigil's existing `--format elf` +
`--keyless` flag wiring). When sigil ships that, the `signing-e2e.yml`
job will start producing a real signed ELF, the test's case 2 will flip
into a positive assertion, and the release workflow can begin attaching
signed firmware to GitHub Releases.

A maintainer who wants to dogfood the synth-side path today can use the
[WASM verification recipe above](#verifying-a-signed-wasm-module-locally),
which exercises the same Fulcio/Rekor surface synth-cli relies on.

## Out of scope

- **Pipeline integration** (Phase 6 territory): wiring `--sign-output` into
  `release.yml` so every published firmware artifact ships signed.
- **Bulk signing of release assets**: at release time the workflow may also
  want to sign the source SBOM, the SHA256SUMS, and other release assets
  — Phase 3 already handles `SHA256SUMS.txt` via cosign keyless.
- **Detached signatures**: synth always asks for an embedded signature
  (`wsc sign` without `--signature-file`). If a consumer wants a detached
  `.sig` they can re-sign separately via `wsc sign -S <path>`.
