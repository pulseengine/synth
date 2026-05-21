//! CycloneDX SBOM emission — a build-time Software Bill of Materials for a
//! compiled ELF. Companion to `safety_manifest.rs`: where the safety manifest
//! records *how* the binary is hardened, the SBOM records *what went into it*.
//!
//! ## Scope
//!
//! synth is a compiler, not a linker, so this is a **build SBOM** — it
//! documents the compilation transaction, not a transitive dependency graph:
//!
//! - `metadata.tools` — the synth compiler itself ("what built it").
//! - the input WASM module — a component with SHA-256 + byte size.
//! - the output ELF binary — a component with SHA-256, size, target triple,
//!   and the backend that produced it.
//! - the WASM module's imports — each imported function/module/memory/etc.
//!   becomes a component, and the output ELF `dependsOn` each of them. This
//!   is the closest synth can get to "what's in the software" without a full
//!   linker view.
//!
//! Explicitly NOT in scope: full transitive scanning of the WASM module,
//! AIBOM/ML-BOM. See `docs/sbom.md`.
//!
//! ## rivet #107 linkage
//!
//! The emitted document is CycloneDX 1.5 JSON. The sibling PulseEngine repo
//! `rivet` (issue #107) defines an `sbom-record` artifact type that ingests a
//! CycloneDX SBOM:
//!
//! ```yaml
//! - id: SBOM-vehicle-control-v1
//!   type: sbom-record
//!   format: cyclonedx
//!   sbom-ref: "sbom/vehicle-control-v1.0.0.cdx.json"
//!   component-count: 142
//! ```
//!
//! The file synth writes here is exactly what `rivet import --format
//! cyclonedx` consumes, becoming one `sbom-record` in the rivet traceability
//! chain.
//!
//! ## Determinism
//!
//! For a fixed set of inputs the document is byte-stable except for
//! `metadata.timestamp`, which is wall-clock by design (a CycloneDX SBOM
//! records when the build happened). The `serialNumber` is derived
//! deterministically from the output ELF's SHA-256, so it too is stable for a
//! given binary.
//!
//! Path convention: when the compiler emits `foo.elf`, the SBOM is written to
//! `foo.cdx.json` next to it.

use crate::wasm_decoder::{ImportEntry, ImportKind};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

/// The CycloneDX spec version this module emits. rivet #107's `sbom-record`
/// ingests 1.5; bump deliberately if the schema shape changes.
const CYCLONEDX_SPEC_VERSION: &str = "1.5";

/// A complete CycloneDX 1.5 SBOM document.
///
/// Field names use `#[serde(rename_all = "camelCase")]` to match the
/// CycloneDX JSON schema (`bomFormat`, `specVersion`, `serialNumber`, ...).
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CycloneDxSbom {
    /// Always the literal string `"CycloneDX"`.
    pub bom_format: String,
    /// CycloneDX spec version — `"1.5"`.
    pub spec_version: String,
    /// `urn:uuid:...` serial number, derived from the output ELF digest.
    pub serial_number: String,
    /// Document revision; `1` for a freshly emitted SBOM.
    pub version: u32,
    /// Build metadata: timestamp + the synth compiler tool entry.
    pub metadata: SbomMetadata,
    /// Components: the input WASM, the output ELF, and one per WASM import.
    pub components: Vec<Component>,
    /// Dependency graph linking the output ELF to its inputs.
    pub dependencies: Vec<Dependency>,
}

/// CycloneDX `metadata` block.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SbomMetadata {
    /// ISO-8601 / RFC-3339 UTC timestamp of when the SBOM was emitted.
    /// The one intentionally non-deterministic field.
    pub timestamp: String,
    /// The tool(s) that produced the described artifact — here, synth itself.
    pub tools: Vec<Tool>,
}

/// CycloneDX `metadata.tools` entry — "what built it".
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Tool {
    /// Tool vendor / publishing organisation.
    pub vendor: String,
    /// Tool name — `"synth"`.
    pub name: String,
    /// Tool version (`CARGO_PKG_VERSION` or a release tag).
    pub version: String,
}

/// A CycloneDX `component`.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Component {
    /// CycloneDX component type (`application`, `library`, ...).
    #[serde(rename = "type")]
    pub component_type: String,
    /// Stable reference used by the `dependencies` graph.
    #[serde(rename = "bom-ref")]
    pub bom_ref: String,
    /// Human-readable component name.
    pub name: String,
    /// Component version (file size for binary artifacts, `"unknown"` for
    /// imports whose version synth cannot know).
    pub version: String,
    /// Cryptographic hashes of the component, when synth has the bytes.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub hashes: Vec<Hash>,
    /// Free-form key/value properties — byte size, target triple, backend,
    /// import kind, etc.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub properties: Vec<Property>,
}

/// A CycloneDX `hashes` entry.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Hash {
    /// Hash algorithm — always `"SHA-256"` here.
    pub alg: String,
    /// Lower-case hex digest.
    pub content: String,
}

/// A CycloneDX `properties` entry — a namespaced key/value pair.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Property {
    /// Property name, namespaced under `synth:`.
    pub name: String,
    /// Property value, always serialised as a string.
    pub value: String,
}

/// A CycloneDX `dependencies` graph node.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Dependency {
    /// The `bom-ref` this node describes.
    #[serde(rename = "ref")]
    pub dep_ref: String,
    /// `bom-ref`s this component depends on.
    #[serde(rename = "dependsOn", skip_serializing_if = "Vec::is_empty")]
    pub depends_on: Vec<String>,
}

/// Inputs needed to construct a build SBOM. Grouped into a struct so the
/// constructor signature stays readable as the SBOM scope grows.
#[derive(Debug, Clone)]
pub struct SbomInputs<'a> {
    /// `CARGO_PKG_VERSION` (or release tag) of the synth that compiled.
    pub synth_version: &'a str,
    /// Path of the input WASM/WAT file (used for the component name).
    pub input_path: &'a Path,
    /// Raw bytes of the input WASM module (post WAT→WASM, pre-compile).
    pub input_bytes: &'a [u8],
    /// Path of the emitted ELF binary.
    pub output_path: &'a Path,
    /// Raw bytes of the emitted ELF binary.
    pub output_bytes: &'a [u8],
    /// LLVM-style target triple of the output (e.g. `thumbv7em-none-eabi`).
    pub target_triple: &'a str,
    /// Name of the backend that produced the ELF (e.g. `arm`, `riscv`).
    pub backend: &'a str,
    /// Imports decoded from the WASM module — one component each.
    pub imports: &'a [ImportEntry],
}

impl CycloneDxSbom {
    /// Build a CycloneDX 1.5 SBOM describing one synth compilation.
    ///
    /// `timestamp` is the RFC-3339 UTC string for `metadata.timestamp`; the
    /// caller supplies it so tests can pin a fixed value and production code
    /// can pass [`now_rfc3339`].
    pub fn new(inputs: &SbomInputs<'_>, timestamp: String) -> Self {
        let input_digest = sha256_hex(inputs.input_bytes);
        let output_digest = sha256_hex(inputs.output_bytes);

        let input_name = file_name_of(inputs.input_path);
        let output_name = file_name_of(inputs.output_path);

        // bom-refs. The output ELF is the root of the dependency graph.
        let input_ref = format!("wasm:{input_name}");
        let output_ref = format!("elf:{output_name}");

        // The input WASM module component.
        let input_component = Component {
            component_type: "library".to_string(),
            bom_ref: input_ref.clone(),
            name: input_name,
            version: format!("{}-bytes", inputs.input_bytes.len()),
            hashes: vec![Hash {
                alg: "SHA-256".to_string(),
                content: input_digest,
            }],
            properties: vec![
                Property {
                    name: "synth:artifact".to_string(),
                    value: "input-wasm".to_string(),
                },
                Property {
                    name: "synth:size-bytes".to_string(),
                    value: inputs.input_bytes.len().to_string(),
                },
            ],
        };

        // The output ELF binary component.
        let output_component = Component {
            component_type: "application".to_string(),
            bom_ref: output_ref.clone(),
            name: output_name,
            version: format!("{}-bytes", inputs.output_bytes.len()),
            hashes: vec![Hash {
                alg: "SHA-256".to_string(),
                content: output_digest.clone(),
            }],
            properties: vec![
                Property {
                    name: "synth:artifact".to_string(),
                    value: "output-elf".to_string(),
                },
                Property {
                    name: "synth:size-bytes".to_string(),
                    value: inputs.output_bytes.len().to_string(),
                },
                Property {
                    name: "synth:target-triple".to_string(),
                    value: inputs.target_triple.to_string(),
                },
                Property {
                    name: "synth:backend".to_string(),
                    value: inputs.backend.to_string(),
                },
            ],
        };

        // One component per WASM import. These are the closest synth can get
        // to "what's linked into" the binary at compile time.
        let mut import_components = Vec::with_capacity(inputs.imports.len());
        let mut import_refs = Vec::with_capacity(inputs.imports.len());
        for imp in inputs.imports {
            let kind = import_kind_str(&imp.kind);
            let bom_ref = format!("import:{}/{}", imp.module, imp.name);
            import_refs.push(bom_ref.clone());
            import_components.push(Component {
                component_type: "library".to_string(),
                bom_ref,
                name: format!("{}::{}", imp.module, imp.name),
                version: "unknown".to_string(),
                hashes: Vec::new(),
                properties: vec![
                    Property {
                        name: "synth:artifact".to_string(),
                        value: "wasm-import".to_string(),
                    },
                    Property {
                        name: "synth:import-kind".to_string(),
                        value: kind.to_string(),
                    },
                    Property {
                        name: "synth:import-module".to_string(),
                        value: imp.module.clone(),
                    },
                ],
            });
        }

        // Dependency graph: the ELF depends on the WASM module and on every
        // import; the WASM module in turn depends on its imports.
        let mut elf_depends_on = Vec::with_capacity(1 + import_refs.len());
        elf_depends_on.push(input_ref.clone());
        elf_depends_on.extend(import_refs.iter().cloned());

        let mut dependencies = vec![
            Dependency {
                dep_ref: output_ref.clone(),
                depends_on: elf_depends_on,
            },
            Dependency {
                dep_ref: input_ref,
                depends_on: import_refs.clone(),
            },
        ];
        // Imports are leaf nodes; declare them with no outgoing edges so the
        // graph is complete (every bom-ref appears as a `ref`).
        for r in import_refs {
            dependencies.push(Dependency {
                dep_ref: r,
                depends_on: Vec::new(),
            });
        }

        let mut components = Vec::with_capacity(2 + import_components.len());
        components.push(output_component);
        components.push(input_component);
        components.extend(import_components);

        CycloneDxSbom {
            bom_format: "CycloneDX".to_string(),
            spec_version: CYCLONEDX_SPEC_VERSION.to_string(),
            // Derive a stable urn:uuid from the output digest so the SBOM is
            // reproducible for a given binary (CycloneDX requires the v4
            // variant/version nibbles, which we stamp in).
            serial_number: uuid_urn_from_digest(&output_digest),
            version: 1,
            metadata: SbomMetadata {
                timestamp,
                tools: vec![Tool {
                    vendor: "PulseEngine".to_string(),
                    name: "synth".to_string(),
                    version: inputs.synth_version.to_string(),
                }],
            },
            components,
            dependencies,
        }
    }

    /// Serialise to pretty-printed CycloneDX 1.5 JSON.
    pub fn to_json(&self) -> String {
        // `serde_json` preserves struct field declaration order, so the
        // output is deterministic (the timestamp aside).
        serde_json::to_string_pretty(self).expect("CycloneDxSbom is always serialisable")
    }

    /// Compute the SBOM path next to an output ELF: replaces the file
    /// extension with `.cdx.json` (the conventional CycloneDX-JSON suffix).
    /// Examples:
    /// - `foo.elf` -> `foo.cdx.json`
    /// - `out`     -> `out.cdx.json`
    pub fn sidecar_path(elf_path: &Path) -> PathBuf {
        let mut p = elf_path.to_path_buf();
        let stem = elf_path
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "out".to_string());
        p.set_file_name(format!("{stem}.cdx.json"));
        p
    }
}

/// Lower-case hex SHA-256 of a byte slice.
fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for b in digest {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// Extract a display file name from a path, falling back to `"unknown"`.
fn file_name_of(path: &Path) -> String {
    path.file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Map an [`ImportKind`] to a stable lower-case string for SBOM properties.
fn import_kind_str(kind: &ImportKind) -> &'static str {
    match kind {
        ImportKind::Function(_) => "function",
        ImportKind::Memory => "memory",
        ImportKind::Table => "table",
        ImportKind::Global => "global",
    }
}

/// Build a CycloneDX `urn:uuid:` serial number deterministically from a
/// SHA-256 hex digest. The first 32 hex chars of the digest fill the UUID,
/// with the version nibble forced to `4` and the variant nibble to `8` so the
/// result is a well-formed RFC-4122 v4 UUID (CycloneDX requires this shape).
fn uuid_urn_from_digest(digest_hex: &str) -> String {
    let h: Vec<char> = digest_hex.chars().take(32).collect();
    debug_assert_eq!(h.len(), 32, "SHA-256 hex digest is 64 chars");
    let s: String = h.iter().collect();
    format!(
        "urn:uuid:{}-{}-4{}-8{}-{}",
        &s[0..8],
        &s[8..12],
        &s[13..16],
        &s[17..20],
        &s[20..32],
    )
}

/// RFC-3339 UTC timestamp for "now", e.g. `2026-05-21T10:30:00Z`.
///
/// Hand-rolled from `SystemTime` (civil-date conversion) to avoid pulling a
/// date/time crate into `synth-core`, which is upstream of every backend.
pub fn now_rfc3339() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    rfc3339_from_unix(secs)
}

/// Convert a Unix timestamp (seconds) to an RFC-3339 UTC string.
/// Uses the standard civil-from-days algorithm (Howard Hinnant).
fn rfc3339_from_unix(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (hour, minute, second) = (rem / 3600, (rem % 3600) / 60, rem % 60);

    // days since 1970-01-01 -> civil (year, month, day)
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = if month <= 2 { year + 1 } else { year };

    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm_decoder::{ImportEntry, ImportKind};
    use std::path::PathBuf;

    /// Fixed timestamp so the rest of the document is fully deterministic.
    const FIXED_TS: &str = "2026-05-21T10:30:00Z";

    fn sample_imports() -> Vec<ImportEntry> {
        vec![
            ImportEntry {
                module: "wasi:cli/stdout".to_string(),
                name: "write".to_string(),
                kind: ImportKind::Function(0),
                index: 0,
            },
            ImportEntry {
                module: "env".to_string(),
                name: "memory".to_string(),
                kind: ImportKind::Memory,
                index: 0,
            },
        ]
    }

    fn sample_sbom() -> CycloneDxSbom {
        let imports = sample_imports();
        let inputs = SbomInputs {
            synth_version: "0.3.1",
            input_path: Path::new("/tmp/vehicle-control.wasm"),
            input_bytes: b"\0asm\x01\0\0\0fake-wasm-body",
            output_path: Path::new("/tmp/vehicle-control.elf"),
            output_bytes: b"\x7fELFfake-elf-body",
            target_triple: "thumbv7em-none-eabi",
            backend: "arm",
            imports: &imports,
        };
        CycloneDxSbom::new(&inputs, FIXED_TS.to_string())
    }

    #[test]
    fn json_has_required_cyclonedx_fields() {
        let json = sample_sbom().to_json();
        let v: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
        assert_eq!(v["bomFormat"], "CycloneDX");
        assert_eq!(v["specVersion"], "1.5");
        assert!(v["serialNumber"].as_str().unwrap().starts_with("urn:uuid:"));
        assert!(v["metadata"].is_object());
        assert!(v["components"].is_array());
        assert!(v["dependencies"].is_array());
        assert_eq!(v["version"], 1);
    }

    #[test]
    fn metadata_tool_is_synth_compiler() {
        let json = sample_sbom().to_json();
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let tool = &v["metadata"]["tools"][0];
        assert_eq!(tool["name"], "synth");
        assert_eq!(tool["vendor"], "PulseEngine");
        assert_eq!(tool["version"], "0.3.1");
        assert_eq!(v["metadata"]["timestamp"], FIXED_TS);
    }

    #[test]
    fn components_cover_wasm_elf_and_imports() {
        let json = sample_sbom().to_json();
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let comps = v["components"].as_array().unwrap();
        // 1 ELF + 1 WASM + 2 imports.
        assert_eq!(comps.len(), 4);

        let elf = &comps[0];
        assert_eq!(elf["type"], "application");
        assert_eq!(elf["name"], "vehicle-control.elf");
        assert_eq!(elf["hashes"][0]["alg"], "SHA-256");
        assert_eq!(elf["hashes"][0]["content"].as_str().unwrap().len(), 64);

        let wasm = &comps[1];
        assert_eq!(wasm["type"], "library");
        assert_eq!(wasm["name"], "vehicle-control.wasm");
        assert_eq!(wasm["hashes"][0]["alg"], "SHA-256");

        // Imports are represented as components.
        let import_names: Vec<&str> = comps[2..]
            .iter()
            .map(|c| c["name"].as_str().unwrap())
            .collect();
        assert!(import_names.contains(&"wasi:cli/stdout::write"));
        assert!(import_names.contains(&"env::memory"));
    }

    #[test]
    fn output_elf_records_target_and_backend() {
        let json = sample_sbom().to_json();
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let props = v["components"][0]["properties"].as_array().unwrap();
        let find = |key: &str| {
            props
                .iter()
                .find(|p| p["name"] == key)
                .map(|p| p["value"].as_str().unwrap().to_string())
        };
        assert_eq!(
            find("synth:target-triple").as_deref(),
            Some("thumbv7em-none-eabi")
        );
        assert_eq!(find("synth:backend").as_deref(), Some("arm"));
        assert_eq!(find("synth:artifact").as_deref(), Some("output-elf"));
    }

    #[test]
    fn dependency_graph_links_elf_to_inputs() {
        let json = sample_sbom().to_json();
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let deps = v["dependencies"].as_array().unwrap();
        // ELF root + WASM + 2 imports = 4 graph nodes.
        assert_eq!(deps.len(), 4);

        // The ELF node depends on the WASM module and every import.
        let elf_node = deps
            .iter()
            .find(|d| d["ref"].as_str().unwrap().starts_with("elf:"))
            .expect("elf dependency node");
        let depends: Vec<&str> = elf_node["dependsOn"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap())
            .collect();
        assert!(depends.iter().any(|d| d.starts_with("wasm:")));
        assert!(depends.iter().any(|d| d.starts_with("import:")));
        assert_eq!(depends.len(), 3); // wasm + 2 imports
    }

    #[test]
    fn serial_number_is_deterministic_for_same_output() {
        // Two SBOMs over identical bytes share a serial number; only the
        // timestamp may differ between emissions.
        let a = sample_sbom();
        let b = sample_sbom();
        assert_eq!(a.serial_number, b.serial_number);
        // Well-formed RFC-4122 v4 shape.
        let uuid = a.serial_number.strip_prefix("urn:uuid:").unwrap();
        let parts: Vec<&str> = uuid.split('-').collect();
        assert_eq!(parts.len(), 5);
        assert!(parts[2].starts_with('4'));
        assert!(parts[3].starts_with('8'));
    }

    #[test]
    fn sidecar_path_strips_elf_extension() {
        let p = CycloneDxSbom::sidecar_path(&PathBuf::from("/tmp/foo.elf"));
        assert_eq!(p, PathBuf::from("/tmp/foo.cdx.json"));
    }

    #[test]
    fn sidecar_path_handles_missing_extension() {
        let p = CycloneDxSbom::sidecar_path(&PathBuf::from("out"));
        assert_eq!(p, PathBuf::from("out.cdx.json"));
    }

    #[test]
    fn sbom_with_no_imports_is_still_valid() {
        let inputs = SbomInputs {
            synth_version: "0.3.1",
            input_path: Path::new("add.wasm"),
            input_bytes: b"\0asm",
            output_path: Path::new("add.elf"),
            output_bytes: b"\x7fELF",
            target_triple: "riscv32imac-unknown-none-elf",
            backend: "riscv",
            imports: &[],
        };
        let sbom = CycloneDxSbom::new(&inputs, FIXED_TS.to_string());
        let v: serde_json::Value = serde_json::from_str(&sbom.to_json()).unwrap();
        // Just the ELF + WASM components, two dependency nodes.
        assert_eq!(v["components"].as_array().unwrap().len(), 2);
        assert_eq!(v["dependencies"].as_array().unwrap().len(), 2);
    }

    #[test]
    fn rfc3339_conversion_is_correct() {
        // 2026-05-21T10:30:00Z == 1779359400 unix seconds.
        assert_eq!(rfc3339_from_unix(1_779_359_400), "2026-05-21T10:30:00Z");
        // Epoch.
        assert_eq!(rfc3339_from_unix(0), "1970-01-01T00:00:00Z");
        // A leap-year date: 2024-02-29T00:00:00Z == 1709164800.
        assert_eq!(rfc3339_from_unix(1_709_164_800), "2024-02-29T00:00:00Z");
    }
}
