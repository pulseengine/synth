//! Safety manifest — sidecar JSON describing the runtime safety checks
//! baked into a compiled ELF. Phase 1 of `docs/binary-safety-design.md` §2.
//!
//! The manifest is intentionally small in Phase 1 (memory bounds + div traps).
//! Later phases extend it with stack-overflow, CFI, prologue, poison, and
//! component-model knobs. The schema is forward-compatible: consumers should
//! treat unknown keys as informational and unknown values as opaque strings.
//!
//! Path convention: when the compiler emits `foo.elf`, it writes
//! `foo.safety-manifest.json` next to it.

use crate::backend::SafetyBounds;
use std::path::{Path, PathBuf};

/// Compile-time safety profile that ends up in the manifest sidecar.
///
/// Each field maps to one row of §3 in the binary-safety design doc; in
/// Phase 1 only `safety_bounds`, `safety_div_zero`, and
/// `safety_div_overflow` carry meaningful values. Other knobs are stubbed
/// as `false`/`"none"` so consumers see the schema shape and can detect
/// when a future synth release turns them on.
#[derive(Debug, Clone)]
pub struct SafetyManifest {
    /// `CARGO_PKG_VERSION` of the synth release that produced the ELF.
    pub synth_version: String,
    /// LLVM-style target triple (e.g. `thumbv7em-none-eabi`,
    /// `riscv32imac-unknown-none-elf`).
    pub target_triple: String,
    /// Memory-bounds enforcement strategy.
    pub safety_bounds: SafetyBounds,
    /// WASM-required divide-by-zero trap is emitted at every i*.div_* /
    /// i*.rem_* site. Phase 1: always `true` on both backends.
    pub safety_div_zero: bool,
    /// WASM-required signed-division overflow (INT_MIN / -1) trap. Phase 1:
    /// `true` on ARM (already shipped) and `true` on RV32 (added this phase).
    pub safety_div_overflow: bool,
    /// Linear-memory size in bytes that the bounds/mask check was sized for.
    /// Recorded so an auditor can spot a manifest/ELF mismatch.
    pub linear_memory_bytes: u32,
}

impl SafetyManifest {
    /// Serialise to pretty-printed JSON. Deliberately handwritten to avoid
    /// pulling `serde_derive` into `synth-core` (which is upstream of every
    /// backend and the proof-extraction toolchain).
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        out.push_str("{\n");
        out.push_str(&format!(
            "  \"synth_version\": {},\n",
            json_string(&self.synth_version)
        ));
        out.push_str(&format!(
            "  \"target_triple\": {},\n",
            json_string(&self.target_triple)
        ));
        out.push_str(&format!(
            "  \"safety_bounds\": {},\n",
            json_string(self.safety_bounds.as_str())
        ));
        out.push_str(&format!(
            "  \"safety_div_zero\": {},\n",
            self.safety_div_zero
        ));
        out.push_str(&format!(
            "  \"safety_div_overflow\": {},\n",
            self.safety_div_overflow
        ));
        out.push_str(&format!(
            "  \"linear_memory_bytes\": {}\n",
            self.linear_memory_bytes
        ));
        out.push_str("}\n");
        out
    }

    /// Compute the manifest path next to an output ELF: replaces the file
    /// extension with `.safety-manifest.json` (or appends it if no extension).
    /// Examples:
    /// - `foo.elf` → `foo.safety-manifest.json`
    /// - `out` → `out.safety-manifest.json`
    pub fn sidecar_path(elf_path: &Path) -> PathBuf {
        let mut p = elf_path.to_path_buf();
        // `set_extension` clobbers the dot before the extension, so emit
        // a compound suffix explicitly.
        let stem = elf_path
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "out".to_string());
        p.set_file_name(format!("{}.safety-manifest.json", stem));
        p
    }
}

/// Minimal JSON-string escaper sufficient for our short, ASCII-only fields.
fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn sample() -> SafetyManifest {
        SafetyManifest {
            synth_version: "0.3.1".to_string(),
            target_triple: "thumbv7em-none-eabi".to_string(),
            safety_bounds: SafetyBounds::Mpu,
            safety_div_zero: true,
            safety_div_overflow: true,
            linear_memory_bytes: 65536,
        }
    }

    #[test]
    fn sidecar_path_strips_elf_extension() {
        let p = SafetyManifest::sidecar_path(&PathBuf::from("/tmp/foo.elf"));
        assert_eq!(p, PathBuf::from("/tmp/foo.safety-manifest.json"));
    }

    #[test]
    fn sidecar_path_handles_missing_extension() {
        let p = SafetyManifest::sidecar_path(&PathBuf::from("out"));
        assert_eq!(p, PathBuf::from("out.safety-manifest.json"));
    }

    #[test]
    fn json_round_trip_shape() {
        let json = sample().to_json();
        assert!(json.contains("\"synth_version\": \"0.3.1\""));
        assert!(json.contains("\"target_triple\": \"thumbv7em-none-eabi\""));
        assert!(json.contains("\"safety_bounds\": \"mpu\""));
        assert!(json.contains("\"safety_div_zero\": true"));
        assert!(json.contains("\"safety_div_overflow\": true"));
        assert!(json.contains("\"linear_memory_bytes\": 65536"));
    }

    #[test]
    fn json_escapes_quotes_in_triple() {
        let m = SafetyManifest {
            target_triple: "weird-\"quoted\"-triple".to_string(),
            ..sample()
        };
        let json = m.to_json();
        assert!(json.contains("weird-\\\"quoted\\\"-triple"));
    }

    #[test]
    fn json_none_bounds_serialises() {
        let m = SafetyManifest {
            safety_bounds: SafetyBounds::None,
            ..sample()
        };
        assert!(m.to_json().contains("\"safety_bounds\": \"none\""));
    }
}
