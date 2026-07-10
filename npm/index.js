#!/usr/bin/env node

// Platform detection and release-asset naming for @pulseengine/synth.
//
// synth is distributed as a single npm package: install.js (postinstall)
// downloads the matching pre-built binary from the GitHub Release whose tag
// equals this package's version, verifies it against the release's signed
// SHA256SUMS manifest, and extracts it into ./bin. This module owns the
// platform -> Rust-target-triple mapping shared by install.js and run.js and
// is the single source of truth for asset names.
//
// Supported targets mirror .github/workflows/release.yml exactly — four
// tarballs, no Windows build:
//   - aarch64-apple-darwin      (macOS arm64)
//   - x86_64-apple-darwin       (macOS x64)
//   - aarch64-unknown-linux-gnu (Linux arm64)
//   - x86_64-unknown-linux-gnu  (Linux x64)

const os = require("os");
const path = require("path");

const REPO = "pulseengine/synth";

/**
 * Map (process.platform, process.arch) to the Rust target triple that
 * release.yml builds and uploads. Throws with a clear message for any
 * combination synth does not ship a binary for (notably Windows, which has
 * no release build — do NOT synthesize a 404 URL for it).
 *
 * @param {string} [platform=os.platform()] node platform id
 * @param {string} [arch=os.arch()] node arch id
 * @returns {string} e.g. "aarch64-apple-darwin"
 */
function getRustTarget(platform = os.platform(), arch = os.arch()) {
  let osTriple;
  switch (platform) {
    case "darwin":
      osTriple = "apple-darwin";
      break;
    case "linux":
      osTriple = "unknown-linux-gnu";
      break;
    default:
      throw new Error(
        `Unsupported platform: ${platform}. synth ships binaries for ` +
          "macOS (darwin) and Linux only. Build from source with " +
          "`cargo install --git https://github.com/pulseengine/synth synth-cli`.",
      );
  }

  let archTriple;
  switch (arch) {
    case "x64":
      archTriple = "x86_64";
      break;
    case "arm64":
      archTriple = "aarch64";
      break;
    default:
      throw new Error(
        `Unsupported architecture: ${arch}. synth ships x86_64 (x64) and ` +
          "aarch64 (arm64) binaries only.",
      );
  }

  return `${archTriple}-${osTriple}`;
}

/**
 * The release-asset tarball name for a given version + platform. Matches the
 * `synth-${VERSION}-${TARGET}.tar.gz` name produced by release.yml, where
 * VERSION is the tag *with* its leading `v` (e.g. v0.38.0).
 *
 * @param {string} version bare semver, e.g. "0.38.0"
 * @param {string} [platform]
 * @param {string} [arch]
 * @returns {string} e.g. "synth-v0.38.0-aarch64-apple-darwin.tar.gz"
 */
function getTarballName(version, platform = os.platform(), arch = os.arch()) {
  const target = getRustTarget(platform, arch);
  return `synth-v${version}-${target}.tar.gz`;
}

/** The binary name inside the tarball / on disk. synth has no Windows build,
 * so there is never a `.exe`. */
function getBinaryName() {
  return "synth";
}

/**
 * Absolute path to the extracted synth binary (populated by install.js).
 */
function getBinaryPath() {
  return path.join(__dirname, "bin", getBinaryName());
}

/**
 * GitHub Release download URL for the platform tarball at this version.
 */
function getTarballUrl(version, platform = os.platform(), arch = os.arch()) {
  const name = getTarballName(version, platform, arch);
  return `https://github.com/${REPO}/releases/download/v${version}/${name}`;
}

/**
 * GitHub Release download URL for the signed SHA256SUMS manifest.
 */
function getChecksumsUrl(version) {
  return `https://github.com/${REPO}/releases/download/v${version}/SHA256SUMS.txt`;
}

/**
 * Parse a SHA256SUMS.txt manifest (as produced by `sha256sum ./*`) into a
 * { basename: hash } map. Each line is `<64-hex-hash>  ./<name>` — note the
 * two-space separator and the `./` path prefix; we key by basename so a
 * caller can look up `synth-v0.38.0-<triple>.tar.gz` directly.
 *
 * @param {string} text raw manifest contents
 * @returns {Map<string,string>}
 */
function parseChecksums(text) {
  const map = new Map();
  for (const rawLine of text.split("\n")) {
    const line = rawLine.trim();
    if (!line) continue;
    const m = line.match(/^([0-9a-fA-F]{64})\s+(.+)$/);
    if (!m) continue;
    const hash = m[1].toLowerCase();
    const name = path.basename(m[2].trim());
    map.set(name, hash);
  }
  return map;
}

/**
 * Look up the expected sha256 for a tarball in a parsed manifest.
 * @returns {string} lowercase hex hash
 * @throws if the tarball is absent from the manifest
 */
function expectedHashFor(tarballName, checksumsText) {
  const map =
    checksumsText instanceof Map ? checksumsText : parseChecksums(checksumsText);
  const hash = map.get(tarballName);
  if (!hash) {
    throw new Error(
      `SHA256SUMS.txt has no entry for ${tarballName} — refusing to install ` +
        "an unverifiable binary.",
    );
  }
  return hash;
}

module.exports = {
  REPO,
  getRustTarget,
  getTarballName,
  getBinaryName,
  getBinaryPath,
  getTarballUrl,
  getChecksumsUrl,
  parseChecksums,
  expectedHashFor,
};

// When invoked directly, print platform info (useful for debugging installs).
if (require.main === module) {
  try {
    const version = require("./package.json").version;
    console.log("synth npm — platform information:");
    console.log(`  Platform:     ${os.platform()}`);
    console.log(`  Architecture: ${os.arch()}`);
    console.log(`  Rust target:  ${getRustTarget()}`);
    console.log(`  Tarball:      ${getTarballName(version)}`);
    console.log(`  Download URL: ${getTarballUrl(version)}`);
    console.log(`  Binary path:  ${getBinaryPath()}`);
  } catch (err) {
    console.error("Error:", err.message);
    process.exit(1);
  }
}
