#!/usr/bin/env node

// Post-install hook for @pulseengine/synth.
//
// Downloads the pre-built `synth` binary for the current platform from the
// GitHub Release whose tag matches this package's version, VERIFIES the
// tarball against the release's SHA256SUMS.txt manifest, then extracts the
// binary into ./bin so run.js can spawn it.
//
// The checksum step is mandatory: an install that cannot verify the archive
// against the published manifest aborts rather than run an unverified binary.
//
// Uses only Node built-ins (https, node:crypto, fs, node:child_process) plus
// the system `tar` — no third-party dependencies.

const os = require("os");
const path = require("path");
const fs = require("fs");
const https = require("https");
const crypto = require("crypto");
const { execFileSync } = require("child_process");

const {
  getRustTarget,
  getBinaryName,
  getBinaryPath,
  getTarballName,
  getTarballUrl,
  getChecksumsUrl,
  expectedHashFor,
} = require("./index.js");

const VERSION = require("./package.json").version;

// Allow air-gapped / offline installs to skip the network fetch (e.g. when a
// binary was pre-placed or is provided by another mechanism).
if (process.env.SYNTH_NPM_SKIP_DOWNLOAD === "1") {
  console.log(
    "SYNTH_NPM_SKIP_DOWNLOAD=1 set — skipping synth binary download.",
  );
  process.exit(0);
}

function download(url, { asBuffer = false, dest = null } = {}, redirects = 0) {
  return new Promise((resolve, reject) => {
    if (redirects > 5) {
      return reject(new Error(`Too many redirects fetching ${url}`));
    }
    https
      .get(url, { headers: { "User-Agent": "pulseengine-synth-npm" } }, (res) => {
        if (
          res.statusCode >= 300 &&
          res.statusCode < 400 &&
          res.headers.location
        ) {
          res.resume();
          return download(res.headers.location, { asBuffer, dest }, redirects + 1)
            .then(resolve)
            .catch(reject);
        }
        if (res.statusCode !== 200) {
          res.resume();
          return reject(
            new Error(`HTTP ${res.statusCode} ${res.statusMessage} for ${url}`),
          );
        }
        if (asBuffer) {
          const chunks = [];
          res.on("data", (c) => chunks.push(c));
          res.on("end", () => resolve(Buffer.concat(chunks)));
          res.on("error", reject);
        } else {
          const file = fs.createWriteStream(dest);
          res.pipe(file);
          file.on("finish", () => file.close(() => resolve(dest)));
          file.on("error", (err) => {
            fs.unlink(dest, () => {});
            reject(err);
          });
        }
      })
      .on("error", reject);
  });
}

function sha256(buffer) {
  return crypto.createHash("sha256").update(buffer).digest("hex");
}

// Extract via execFile (no shell) — inputs are paths we constructed, but the
// argv form is the correct idiom regardless.
function extractTarball(archivePath, destDir) {
  execFileSync("tar", ["-xzf", archivePath, "-C", destDir], {
    stdio: "inherit",
  });
}

async function main() {
  const target = getRustTarget();
  const tarballName = getTarballName(VERSION);
  const tarballUrl = getTarballUrl(VERSION);
  const checksumsUrl = getChecksumsUrl(VERSION);
  const binaryName = getBinaryName();

  console.log(`synth npm installer — v${VERSION}`);
  console.log(`  Platform: ${os.type()} ${os.arch()} (${target})`);
  console.log(`  Tarball:  ${tarballName}`);

  const binDir = path.join(__dirname, "bin");
  fs.mkdirSync(binDir, { recursive: true });
  const archivePath = path.join(binDir, tarballName);

  // 1. Fetch the signed checksum manifest first, so we know what to expect.
  console.log("  Fetching SHA256SUMS.txt ...");
  const checksumsText = (await download(checksumsUrl, { asBuffer: true })).toString(
    "utf8",
  );
  const expected = expectedHashFor(tarballName, checksumsText);

  // 2. Download the tarball.
  console.log(`  Downloading ${tarballUrl} ...`);
  await download(tarballUrl, { dest: archivePath });

  // 3. Verify BEFORE extracting.
  const actual = sha256(fs.readFileSync(archivePath));
  if (actual !== expected) {
    fs.unlinkSync(archivePath);
    throw new Error(
      `Checksum mismatch for ${tarballName}\n` +
        `  expected: ${expected}\n` +
        `  actual:   ${actual}\n` +
        "The download may be corrupted or tampered with. Aborting.",
    );
  }
  console.log(`  Checksum OK (sha256 ${actual}).`);

  // 4. Extract and expose the binary.
  console.log("  Extracting ...");
  extractTarball(archivePath, binDir);
  fs.unlinkSync(archivePath);

  const binaryPath = getBinaryPath();
  if (!fs.existsSync(binaryPath)) {
    throw new Error(
      `Extraction succeeded but ${binaryName} was not found at ${binaryPath}.`,
    );
  }
  fs.chmodSync(binaryPath, 0o755);
  console.log(`  Installed synth -> ${binaryPath}`);
}

main().catch((err) => {
  console.error("");
  console.error("Failed to install the synth binary:", err.message);
  console.error("");
  console.error("Alternatives:");
  console.error(
    "  1. Build from source: cargo install --git " +
      "https://github.com/pulseengine/synth synth-cli",
  );
  console.error(
    "  2. Download a release manually: " +
      "https://github.com/pulseengine/synth/releases",
  );
  // A failed binary install is a hard error: unlike rivet (which has a
  // platform-package primary path and treats the download as a fallback),
  // this package's ONLY delivery mechanism is the verified download. If it
  // fails, `synth` would not exist — surface that loudly.
  process.exit(1);
});
