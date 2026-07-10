"use strict";

// Unit tests for @pulseengine/synth's platform -> release-asset mapping and
// the SHA256SUMS parser. Node built-in test runner only (no dev deps):
//   npm test          (package.json runs `node --test`)
//   node --test test/mapping.test.js

const test = require("node:test");
const assert = require("node:assert/strict");

const {
  getRustTarget,
  getTarballName,
  getTarballUrl,
  getChecksumsUrl,
  getBinaryName,
  parseChecksums,
  expectedHashFor,
} = require("../index.js");

test("platform x arch -> Rust target triple (the four shipped targets)", () => {
  assert.equal(getRustTarget("darwin", "arm64"), "aarch64-apple-darwin");
  assert.equal(getRustTarget("darwin", "x64"), "x86_64-apple-darwin");
  assert.equal(getRustTarget("linux", "arm64"), "aarch64-unknown-linux-gnu");
  assert.equal(getRustTarget("linux", "x64"), "x86_64-unknown-linux-gnu");
});

test("darwin/arm64 maps to the exact v0.38.0 tarball name", () => {
  assert.equal(
    getTarballName("0.38.0", "darwin", "arm64"),
    "synth-v0.38.0-aarch64-apple-darwin.tar.gz",
  );
});

test("tarball URL points at the versioned GitHub release asset", () => {
  assert.equal(
    getTarballUrl("0.38.0", "linux", "x64"),
    "https://github.com/pulseengine/synth/releases/download/v0.38.0/" +
      "synth-v0.38.0-x86_64-unknown-linux-gnu.tar.gz",
  );
  assert.equal(
    getChecksumsUrl("0.38.0"),
    "https://github.com/pulseengine/synth/releases/download/v0.38.0/SHA256SUMS.txt",
  );
});

test("binary name is always 'synth' (no Windows build)", () => {
  assert.equal(getBinaryName(), "synth");
});

test("unsupported platforms/arches throw a clear error (no 404 URL)", () => {
  assert.throws(() => getRustTarget("win32", "x64"), /Unsupported platform: win32/);
  assert.throws(() => getRustTarget("freebsd", "x64"), /Unsupported platform/);
  assert.throws(() => getRustTarget("linux", "ia32"), /Unsupported architecture: ia32/);
  assert.throws(() => getRustTarget("darwin", "riscv64"), /Unsupported architecture/);
});

// The real v0.38.0 manifest is produced by `sha256sum ./*`: two-space
// separator, a `./` path prefix, one entry per asset. Parsing must key by
// basename so a lookup by tarball name succeeds.
const REAL_SHA256SUMS = [
  "6e280e09614026ae9ca8378d3f5d9c038ea5f9bb0a43cdfaff9d3f60bbbaf437  ./synth-0.38.0.cdx.json",
  "c2208c039c0b646de3c1dec02b6dc5c26271fce338be58012859528eaf7d1601  ./synth-v0.38.0-aarch64-apple-darwin.tar.gz",
  "77c123b8bc663c0fd91521d7874a8521ae29b3f1b61f761c1b059b3ea29cb410  ./synth-v0.38.0-aarch64-unknown-linux-gnu.tar.gz",
  "b1750e5a5cfc2306ca79e5bfeb250f93e518f9ff8539465286e9e50580f369f0  ./synth-v0.38.0-x86_64-apple-darwin.tar.gz",
  "69e0327d566ab4e767b386019c395457fc261e3ff2f0d85587f71ddd738f95d5  ./synth-v0.38.0-x86_64-unknown-linux-gnu.tar.gz",
  "",
].join("\n");

test("parseChecksums keys by basename, strips the ./ prefix", () => {
  const map = parseChecksums(REAL_SHA256SUMS);
  assert.equal(map.size, 5);
  assert.equal(
    map.get("synth-v0.38.0-aarch64-apple-darwin.tar.gz"),
    "c2208c039c0b646de3c1dec02b6dc5c26271fce338be58012859528eaf7d1601",
  );
});

test("expectedHashFor resolves the darwin/arm64 tarball from the real manifest", () => {
  const name = getTarballName("0.38.0", "darwin", "arm64");
  assert.equal(
    expectedHashFor(name, REAL_SHA256SUMS),
    "c2208c039c0b646de3c1dec02b6dc5c26271fce338be58012859528eaf7d1601",
  );
});

test("expectedHashFor throws when a tarball is absent from the manifest", () => {
  assert.throws(
    () => expectedHashFor("synth-v9.9.9-x86_64-apple-darwin.tar.gz", REAL_SHA256SUMS),
    /no entry for/,
  );
});
