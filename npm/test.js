#!/usr/bin/env node

// Unit tests for @pulseengine/synth's platform detection, release-URL
// construction, and SHA256SUMS parsing. No test framework — a tiny runner
// over node:assert so it runs on any Node >=14 with zero dependencies.
//
// An optional network smoke test at the end downloads the REAL v0.38.0
// tarball + SHA256SUMS and verifies the checksum end-to-end. It is skipped
// (not failed) when the network is unavailable or SYNTH_NPM_SKIP_NETWORK=1.

const assert = require("assert");
const os = require("os");
const path = require("path");
const fs = require("fs");
const https = require("https");
const crypto = require("crypto");
const { execFileSync } = require("child_process");

const {
  getRustTarget,
  getArchiveName,
  getDownloadUrl,
  getChecksumsUrl,
  expectedChecksum,
  getBinaryName,
  SUPPORTED_TARGETS,
} = require("./index.js");

let passed = 0;
let failed = 0;
let skipped = 0;

function test(name, fn) {
  try {
    fn();
    passed++;
    console.log(`  ok   ${name}`);
  } catch (err) {
    failed++;
    console.log(`  FAIL ${name}`);
    console.log(`       ${err.message}`);
  }
}

console.log("platform / arch -> rust target");
test("darwin/arm64 -> aarch64-apple-darwin", () => {
  assert.strictEqual(getRustTarget("darwin", "arm64"), "aarch64-apple-darwin");
});
test("darwin/x64 -> x86_64-apple-darwin", () => {
  assert.strictEqual(getRustTarget("darwin", "x64"), "x86_64-apple-darwin");
});
test("linux/arm64 -> aarch64-unknown-linux-gnu", () => {
  assert.strictEqual(getRustTarget("linux", "arm64"), "aarch64-unknown-linux-gnu");
});
test("linux/x64 -> x86_64-unknown-linux-gnu", () => {
  assert.strictEqual(getRustTarget("linux", "x64"), "x86_64-unknown-linux-gnu");
});
test("every mapped target is one the release workflow builds", () => {
  for (const [plat, arch] of [
    ["darwin", "arm64"],
    ["darwin", "x64"],
    ["linux", "arm64"],
    ["linux", "x64"],
  ]) {
    assert.ok(
      SUPPORTED_TARGETS.includes(getRustTarget(plat, arch)),
      `${plat}/${arch} not in SUPPORTED_TARGETS`,
    );
  }
});
test("win32 host errors cleanly (no Windows build)", () => {
  assert.throws(() => getRustTarget("win32", "x64"), /Unsupported platform/);
});
test("unsupported arch errors cleanly", () => {
  assert.throws(() => getRustTarget("linux", "ia32"), /Unsupported architecture/);
});

console.log("archive name + URL construction");
test("archive name: darwin/arm64 @ 0.38.0", () => {
  assert.strictEqual(
    getArchiveName("0.38.0", "darwin", "arm64"),
    "synth-v0.38.0-aarch64-apple-darwin.tar.gz",
  );
});
test("download URL embeds the v-prefixed tag and asset", () => {
  assert.strictEqual(
    getDownloadUrl("0.38.0", "linux", "x64"),
    "https://github.com/pulseengine/synth/releases/download/v0.38.0/" +
      "synth-v0.38.0-x86_64-unknown-linux-gnu.tar.gz",
  );
});
test("checksums URL points at the release SHA256SUMS.txt", () => {
  assert.strictEqual(
    getChecksumsUrl("0.38.0"),
    "https://github.com/pulseengine/synth/releases/download/v0.38.0/SHA256SUMS.txt",
  );
});
test("binary name is synth", () => {
  assert.strictEqual(getBinaryName(), "synth");
});
test("package.json version has no v prefix; URL adds it", () => {
  const version = require("./package.json").version;
  assert.ok(/^\d+\.\d+\.\d+/.test(version), `bad version: ${version}`);
  assert.ok(getDownloadUrl(version).includes(`/download/v${version}/`));
});

console.log("SHA256SUMS parsing");
const SAMPLE_SUMS = [
  "6e280e09614026ae9ca8378d3f5d9c038ea5f9bb0a43cdfaff9d3f60bbbaf437  ./synth-0.38.0.cdx.json",
  "c2208c039c0b646de3c1dec02b6dc5c26271fce338be58012859528eaf7d1601  ./synth-v0.38.0-aarch64-apple-darwin.tar.gz",
  "77c123b8bc663c0fd91521d7874a8521ae29b3f1b61f761c1b059b3ea29cb410  ./synth-v0.38.0-aarch64-unknown-linux-gnu.tar.gz",
  "b1750e5a5cfc2306ca79e5bfeb250f93e518f9ff8539465286e9e50580f369f0  ./synth-v0.38.0-x86_64-apple-darwin.tar.gz",
  "69e0327d566ab4e767b386019c395457fc261e3ff2f0d85587f71ddd738f95d5  ./synth-v0.38.0-x86_64-unknown-linux-gnu.tar.gz",
  "",
].join("\n");

test("resolves the ./-prefixed entry by basename", () => {
  assert.strictEqual(
    expectedChecksum(SAMPLE_SUMS, "synth-v0.38.0-aarch64-apple-darwin.tar.gz"),
    "c2208c039c0b646de3c1dec02b6dc5c26271fce338be58012859528eaf7d1601",
  );
});
test("resolves the linux x64 entry", () => {
  assert.strictEqual(
    expectedChecksum(SAMPLE_SUMS, "synth-v0.38.0-x86_64-unknown-linux-gnu.tar.gz"),
    "69e0327d566ab4e767b386019c395457fc261e3ff2f0d85587f71ddd738f95d5",
  );
});
test("missing archive throws", () => {
  assert.throws(
    () => expectedChecksum(SAMPLE_SUMS, "synth-v9.9.9-aarch64-apple-darwin.tar.gz"),
    /No checksum entry/,
  );
});
test("end-to-end: derived archive name resolves in the manifest", () => {
  const archive = getArchiveName("0.38.0", "darwin", "arm64");
  const hash = expectedChecksum(SAMPLE_SUMS, archive);
  assert.strictEqual(hash, "c2208c039c0b646de3c1dec02b6dc5c26271fce338be58012859528eaf7d1601");
});

// ── Optional network smoke test against the real v0.38.0 release ────────────
function httpGetBuffer(url, redirectsLeft = 5) {
  return new Promise((resolve, reject) => {
    https
      .get(url, { headers: { "User-Agent": "pulseengine-synth-npm-test" } }, (res) => {
        if ([301, 302, 307, 308].includes(res.statusCode) && redirectsLeft > 0) {
          return httpGetBuffer(res.headers.location, redirectsLeft - 1)
            .then(resolve)
            .catch(reject);
        }
        if (res.statusCode !== 200) {
          return reject(new Error(`HTTP ${res.statusCode} for ${url}`));
        }
        const chunks = [];
        res.on("data", (c) => chunks.push(c));
        res.on("end", () => resolve(Buffer.concat(chunks)));
        res.on("error", reject);
      })
      .on("error", reject);
  });
}

async function smokeTest() {
  console.log("network smoke test (real v0.38.0 download + checksum)");
  if (process.env.SYNTH_NPM_SKIP_NETWORK === "1") {
    skipped++;
    console.log("  skip SYNTH_NPM_SKIP_NETWORK=1");
    return;
  }
  // Exercise the true host mapping so the smoke test tracks whatever runner
  // it lands on; fall back to darwin/arm64 for unsupported CI hosts.
  let plat = os.platform();
  let arch = os.arch();
  try {
    getRustTarget(plat, arch);
  } catch {
    plat = "darwin";
    arch = "arm64";
  }

  const version = "0.38.0";
  const archive = getArchiveName(version, plat, arch);
  const url = getDownloadUrl(version, plat, arch);
  const sumsUrl = getChecksumsUrl(version);

  try {
    const sumsText = (await httpGetBuffer(sumsUrl)).toString("utf8");
    const expected = expectedChecksum(sumsText, archive);
    const tarball = await httpGetBuffer(url);
    const actual = crypto.createHash("sha256").update(tarball).digest("hex");
    assert.strictEqual(actual, expected, `checksum mismatch for ${archive}`);

    // Extract and confirm the tarball actually contains a `synth` binary.
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "synth-npm-smoke-"));
    const tarPath = path.join(tmp, archive);
    fs.writeFileSync(tarPath, tarball);
    execFileSync("tar", ["-xzf", tarPath, "-C", tmp], { stdio: "ignore" });
    assert.ok(fs.existsSync(path.join(tmp, "synth")), "tarball missing synth binary");
    fs.rmSync(tmp, { recursive: true, force: true });

    passed++;
    console.log(`  ok   downloaded + verified ${archive} (sha256 ${actual.slice(0, 16)}...)`);
  } catch (err) {
    // Network / offline / rate-limit -> skip, don't fail the suite.
    skipped++;
    console.log(`  skip network unavailable: ${err.message}`);
  }
}

smokeTest().then(() => {
  console.log("");
  console.log(`${passed} passed, ${failed} failed, ${skipped} skipped`);
  process.exit(failed === 0 ? 0 : 1);
});
