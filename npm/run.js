#!/usr/bin/env node

// Thin launcher that spawns the synth binary extracted by install.js.
// Forwards argv, stdio, and exit code; propagates signals to the child.

const { spawn } = require("child_process");
const fs = require("fs");
const { getBinaryPath } = require("./index.js");

const binaryPath = getBinaryPath();

if (!fs.existsSync(binaryPath)) {
  console.error("synth binary not found at:", binaryPath);
  console.error("");
  console.error("This usually means the postinstall download did not run or");
  console.error("failed. Try reinstalling:");
  console.error("  npm install --force @pulseengine/synth");
  console.error("");
  console.error(
    "Or build from source: cargo install --git " +
      "https://github.com/pulseengine/synth synth-cli",
  );
  process.exit(1);
}

const child = spawn(binaryPath, process.argv.slice(2), {
  stdio: "inherit",
  env: process.env,
});

child.on("error", (err) => {
  console.error("Failed to start synth:", err.message);
  process.exit(1);
});

child.on("exit", (code, signal) => {
  if (signal) {
    process.kill(process.pid, signal);
  } else {
    process.exit(code == null ? 0 : code);
  }
});

process.on("SIGINT", () => child.kill("SIGINT"));
process.on("SIGTERM", () => child.kill("SIGTERM"));
