#!/usr/bin/env node

// Pre-uninstall hook: remove the binary downloaded into ./bin by install.js.

const fs = require("fs");
const path = require("path");

const binDir = path.join(__dirname, "bin");

if (fs.existsSync(binDir)) {
  try {
    fs.rmSync(binDir, { recursive: true, force: true });
  } catch (err) {
    console.error("Failed to clean synth bin/:", err.message);
  }
}
