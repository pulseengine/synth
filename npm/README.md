# @pulseengine/synth

`synth` — a WebAssembly-to-native compiler with mechanized correctness proofs
in Rocq. It compiles WebAssembly to bare-metal ELF binaries for ARM Cortex-M
(Thumb-2), Cortex-R5 (A32), RISC-V (RV32IMAC), and host-native AArch64.

This npm package distributes the `synth` CLI binary so it can be installed and
invoked from any Node.js environment. It complements the crates.io
distribution (`cargo install synth-cli`).

## Install

```bash
# One-shot (no install)
npx @pulseengine/synth --version

# Global install
npm install -g @pulseengine/synth
synth --version
```

## How it works

There are no third-party dependencies. On install, the `postinstall` hook:

1. Detects your platform and architecture.
2. Downloads the matching `synth-v<version>-<triple>.tar.gz` from the GitHub
   Release whose tag equals this package's version.
3. **Verifies** the tarball's SHA-256 against the release's signed
   `SHA256SUMS.txt` manifest — a mismatch aborts the install.
4. Extracts the `synth` binary into the package's `bin/` directory.

The package version tracks the synth release version, so
`npm install @pulseengine/synth@0.38.0` fetches the `v0.38.0` binaries.

Set `SYNTH_NPM_SKIP_DOWNLOAD=1` to skip the download (e.g. air-gapped CI where
the binary is provided out of band).

## Supported platforms

Mirrors the release build matrix (no Windows build):

- `darwin-arm64` — `aarch64-apple-darwin`
- `darwin-x64` — `x86_64-apple-darwin`
- `linux-arm64` — `aarch64-unknown-linux-gnu`
- `linux-x64` — `x86_64-unknown-linux-gnu`

Binaries are pre-built and published alongside each GitHub release at
<https://github.com/pulseengine/synth/releases>. On an unsupported platform,
install from source:

```bash
cargo install --git https://github.com/pulseengine/synth synth-cli
```

## License

Apache-2.0. See the [repository](https://github.com/pulseengine/synth) for
source, documentation, and issues.
