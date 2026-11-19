//! `synth compile -b x86_64` — RQ-91-X86SKEL (#1741, VCR-X86-001).
//!
//! The x86-64 backend does NOT go through `compile_command`. That function is
//! the ARM/RV32/AArch64 pipeline, and almost every flag it honours (startup
//! images, MPU layouts, WCET, DWARF, provenance, SBOM, signing, the
//! native-pointer ABI, embedder-init contracts, ...) has no x86-64 meaning in
//! lane X1. Routing x86-64 through it would make each of those flags a silent
//! no-op on x86-64 unless every one of them grew an x86 arm. Instead the
//! dispatcher sends `-b x86_64` here BEFORE any of that runs, and this path
//! accepts exactly:
//!
//! - the input (`.wat` or `.wasm`) and `-o`;
//! - `--relocatable` and `--all-exports`, which describe what this path always
//!   does (one ELF64 `ET_REL`, every function lowered) and so change nothing;
//! - `--target x86_64` / `x86_64-none-elf` (the only x86-64 profile);
//! - `--safety-bounds software|none`: the module may not have a memory in this
//!   lane, so neither mode can emit anything; `mask`, `mpu` and `pmp` are
//!   refused, as on AArch64.
//!
//! Every other flag that was given is REFUSED BY NAME, and no object is
//! written. The other backends never reach this file, so their output is
//! untouched by it.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use synth_core::backend::SafetyBounds;
use synth_core::target::{ArchFamily, TargetSpec};

/// Compile `input` for x86-64. `set_flags` names every flag the user gave
/// that this path does not accept (the dispatcher builds it from the parsed
/// arguments); any entry is a refusal.
pub(crate) fn compile(
    input: Option<&Path>,
    output: &Path,
    target: Option<&str>,
    safety_bounds: Option<&str>,
    set_flags: &[&str],
) -> Result<()> {
    if !set_flags.is_empty() {
        anyhow::bail!(
            "-b x86_64 does not support {} (RQ-91-X86SKEL, #1741: the x86-64 \
             backend is a skeleton that lowers leaf i32 functions into an ELF64 \
             ET_REL; it accepts only the input, -o, --relocatable, --all-exports, \
             --target x86_64 and --safety-bounds software|none) — refusing",
            set_flags.join(", ")
        );
    }
    if let Some(name) = target {
        let spec = TargetSpec::from_triple(name).map_err(|e| anyhow::anyhow!("{e}"))?;
        if spec.family != ArchFamily::X86_64 {
            anyhow::bail!(
                "backend 'x86_64' does not accept --target {name}.\n\
                 targets accepted by backend 'x86_64': x86_64"
            );
        }
    }
    if let Some(mode) = safety_bounds {
        match SafetyBounds::parse(mode).map_err(|e| anyhow::anyhow!(e))? {
            SafetyBounds::Software | SafetyBounds::None => {}
            other => anyhow::bail!(
                "--safety-bounds {} is not implemented on the x86_64 backend — \
                 refusing rather than silently emitting unchecked accesses. \
                 Use software (the default) or none.",
                other.as_str()
            ),
        }
    }
    let path: PathBuf = input
        .context("-b x86_64 needs an input module (.wat or .wasm)")?
        .to_path_buf();
    let wasm = if path.extension().is_some_and(|e| e == "wast") {
        anyhow::bail!(
            "-b x86_64 does not compile .wast scripts (RQ-91-X86SKEL); pass a \
             .wat or .wasm module"
        );
    } else if path.extension().is_some_and(|e| e == "wat") {
        wat::parse_file(&path).with_context(|| format!("failed to parse {}", path.display()))?
    } else {
        let bytes =
            std::fs::read(&path).with_context(|| format!("failed to read {}", path.display()))?;
        if bytes.starts_with(b"\0asm") {
            bytes
        } else {
            wat::parse_bytes(&bytes)
                .with_context(|| format!("failed to parse {}", path.display()))?
                .into_owned()
        }
    };
    let obj = synth_backend_x86_64::compile_wasm(&wasm).map_err(|e| anyhow::anyhow!("{e}"))?;
    std::fs::write(output, &obj.elf)
        .with_context(|| format!("failed to write {}", output.display()))?;
    let exported: Vec<&str> = obj
        .functions
        .iter()
        .flat_map(|f| f.symbols.iter().skip(1).map(String::as_str))
        .collect();
    println!(
        "Wrote x86_64 ELF64 relocatable object {} ({} bytes, {} function(s); exports: {})",
        output.display(),
        obj.elf.len(),
        obj.functions.len(),
        exported.join(", ")
    );
    Ok(())
}
