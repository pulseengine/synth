//! RQ-91-MPUENFORCE (#1145): `--emit-memory-facts` — write the
//! `synth-memfacts-v1` sidecar (`<output>.memfacts.json`) for a multi-memory
//! ARM `--relocatable` object.
//!
//! WHY A SIDECAR AND NOT A SECTION. gale's consumer is a BUILD-TIME gate,
//! outside the flight TCB, so the facts never need to reach the target; and
//! a section would be the wrong carrier for three measured reasons:
//!   * it changes the object's bytes, and the `--safety-bounds mpu
//!     --embedder-mpu` object is pinned byte-identical to the plain one
//!     (`mem_isolation_red_1145.py`); a sidecar leaves every object byte-
//!     identical whether or not the flag is passed;
//!   * a linker concatenates same-named non-alloc sections across inputs (or
//!     drops them under `--gc-sections`), so per-object facts would lose their
//!     attribution in the linked image gale actually inspects;
//!   * it is the existing shape: `--emit-wcet`, `--emit-stack-depth` and
//!     `--emit-provenance` are all JSON sidecars next to the output.
//!
//! The sidecar carries the object's sha256, so a stale sidecar beside a
//! rebuilt object is detectable.
//!
//! DERIVED FROM THE ARTIFACT. Every bound is READ BACK from the written
//! object — `__synth_mem_count`, `__synth_mem_size_k`, `__synth_mem_region_k`
//! and `__synth_mem_base_k` with its section's `sh_addralign`/`sh_size` — not
//! recomputed, so the sidecar cannot disagree with what ships. The memory
//! sets come from the decoded wasm (the memory index of every access is a
//! static immediate) and are then CROSS-CHECKED against the object: the
//! functions described are exactly the `func_N` bodies the object defines,
//! every export name is a symbol of the object, and every relocation inside
//! a function's own code that names memory k's base or size symbol (k >= 1)
//! finds k in that function's direct set. A disagreement refuses the compile
//! instead of writing facts.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SymbolSection};
use synth_core::memory_facts::{
    self, BaseSource, DomainMap, FunctionInput, MEMORY_FACTS_SCHEMA, MemoryBounds,
    MemoryFactsReport, MpuLayout,
};

/// `<output>.memfacts.json`.
pub fn sidecar_path(output: &Path) -> PathBuf {
    let mut s = output.as_os_str().to_os_string();
    s.push(".memfacts.json");
    PathBuf::from(s)
}

/// Refuse a request this path cannot honour, BEFORE compiling.
#[allow(clippy::too_many_arguments)]
pub fn check_request(
    emit: bool,
    domain_specs: &[String],
    layout: Option<MpuLayout>,
    backend: &str,
    relocatable: bool,
    all_exports: bool,
    input: Option<&Path>,
    loom: bool,
) -> Result<()> {
    if !domain_specs.is_empty() && !emit {
        bail!(
            "--memory-domain names the domains of the --emit-memory-facts sidecar; \
             without --emit-memory-facts it would mean nothing — refusing"
        );
    }
    let what = match (emit, layout) {
        (true, _) => "--emit-memory-facts",
        (false, Some(_)) => "--mpu-layout",
        (false, None) => return Ok(()),
    };
    if backend != "arm" || !relocatable {
        bail!(
            "{what} (#1145) applies to an ARM `--relocatable` object only: that is the \
             one path that compiles a multi-memory module and carries the per-memory \
             region table it describes"
        );
    }
    if emit && !all_exports {
        bail!(
            "--emit-memory-facts (#1145) needs --all-exports: the facts describe every \
             function the object defines"
        );
    }
    if emit && loom {
        bail!(
            "--emit-memory-facts (#1145) is refused with --loom: the facts are derived \
             from the input module's function bodies, and loom rewrites them before \
             synth compiles"
        );
    }
    if let Some(p) = input
        && p.extension().is_some_and(|e| e == "wast")
    {
        bail!("{what} (#1145) is refused on a .wast input: compile the module as .wat/.wasm");
    }
    Ok(())
}

struct ObjSym {
    section: Option<object::SectionIndex>,
    absolute: bool,
    value: u64,
    size: u64,
}

/// Read the object back and write the sidecar.
pub fn emit(
    input: &Path,
    output: &Path,
    target: &str,
    native_pointer_abi: bool,
    domain_specs: &[String],
    layout: Option<MpuLayout>,
) -> Result<PathBuf> {
    let file_bytes =
        std::fs::read(input).with_context(|| format!("reading {}", input.display()))?;
    let wasm = wat::parse_bytes(&file_bytes).context("parsing the input module")?;
    let module = synth_core::wasm_decoder::decode_wasm_module(&wasm)
        .context("decoding the input module for --emit-memory-facts")?;
    let index_space = module.memory_index_space();
    let decoded_count = index_space.len() as u32;
    let imported_count = module.imported_memories.len() as u32;

    let obj_bytes =
        std::fs::read(output).with_context(|| format!("reading back {}", output.display()))?;
    let obj = object::File::parse(&*obj_bytes).context("parsing the written object")?;
    let mut syms: BTreeMap<String, ObjSym> = BTreeMap::new();
    let mut sym_names: BTreeMap<usize, String> = BTreeMap::new();
    for s in obj.symbols() {
        let Ok(name) = s.name() else { continue };
        if name.is_empty() {
            continue;
        }
        sym_names.insert(s.index().0, name.to_string());
        let (section, absolute) = match s.section() {
            SymbolSection::Section(i) => (Some(i), false),
            SymbolSection::Absolute => (None, true),
            _ => continue,
        };
        syms.insert(
            name.to_string(),
            ObjSym {
                section,
                absolute,
                value: s.address(),
                size: s.size(),
            },
        );
    }
    let abs = |name: &str| -> Result<u32> {
        match syms.get(name) {
            Some(s) if s.absolute => Ok(s.value as u32),
            _ => bail!(
                "--emit-memory-facts (#1145): the object has no absolute `{name}` — it \
                 does not carry the multi-memory region table these facts are read from"
            ),
        }
    };

    let memory_count = abs("__synth_mem_count").map_err(|_| {
        anyhow::anyhow!(
            "--emit-memory-facts (#1145): the module has {decoded_count} linear \
             memory(ies) and the object carries no region table; the facts exist for a \
             multi-memory object, whose grants differ per memory"
        )
    })?;
    if memory_count != decoded_count {
        bail!(
            "--emit-memory-facts (#1145): the object's __synth_mem_count is \
             {memory_count} but the module declares {decoded_count} memories — refusing \
             to describe an object the module does not match"
        );
    }
    let domains = DomainMap::parse(domain_specs, memory_count).map_err(anyhow::Error::msg)?;

    // Bounds, read back per memory.
    let mut memories = Vec::new();
    // Symbols whose relocation inside a function's code names memory k.
    let mut mem_of_symbol: BTreeMap<String, u32> = BTreeMap::new();
    for k in 0..memory_count {
        let size_symbol = format!("__synth_mem_size_{k}");
        let region_symbol = format!("__synth_mem_region_{k}");
        let size_bytes = abs(&size_symbol)?;
        let region = abs(&region_symbol)?;
        let (base, section_align, section_bytes) = if k == 0 {
            if native_pointer_abi {
                let statics = match syms.get("__synth_wasm_data") {
                    Some(s) => {
                        let sec = obj.section_by_index(
                            s.section.context("__synth_wasm_data has no section")?,
                        )?;
                        Some(sec.name()?.to_string())
                    }
                    None => None,
                };
                (
                    BaseSource::Native {
                        statics_symbol: statics.as_ref().map(|_| "__synth_wasm_data".to_string()),
                        statics_section: statics,
                    },
                    None,
                    None,
                )
            } else {
                (
                    BaseSource::Register {
                        register: "r11".to_string(),
                    },
                    None,
                    None,
                )
            }
        } else {
            let base_symbol = format!("__synth_mem_base_{k}");
            let s = syms.get(&base_symbol).with_context(|| {
                format!(
                    "--emit-memory-facts (#1145): memory {k} has no `{base_symbol}` in the \
                     object, so its base has no source to name — refusing"
                )
            })?;
            let sec = obj.section_by_index(s.section.context("base symbol has no section")?)?;
            if s.value != 0 {
                bail!(
                    "--emit-memory-facts (#1145): `{base_symbol}` is not at offset 0 of its section"
                );
            }
            mem_of_symbol.insert(base_symbol.clone(), k);
            mem_of_symbol.insert(size_symbol.clone(), k);
            mem_of_symbol.insert(format!("__synth_wasm_data_{k}"), k);
            (
                BaseSource::Symbol {
                    symbol: base_symbol,
                    section: sec.name()?.to_string(),
                },
                Some(sec.align() as u32),
                Some(sec.size() as u32),
            )
        };
        memories.push(MemoryBounds {
            index: k,
            imported: k < imported_count,
            size_bytes,
            size_symbol,
            base,
            section_align,
            section_bytes,
            pmsav7_region_bytes: region,
            region_symbol,
            pmsav7_subregions_enabled: section_bytes
                .and_then(|b| memory_facts::subregions_enabled(b, region)),
            pmsav8_granule_bytes: 32,
            domain: domains.domain_of(k).map(str::to_string),
        });
    }

    // Functions: exactly the bodies the object defines.
    let shipped: BTreeSet<u32> = syms
        .keys()
        .filter_map(|n| n.strip_prefix("func_")?.parse().ok())
        .collect();
    let inputs: Vec<FunctionInput<'_>> = module
        .functions
        .iter()
        .filter(|f| shipped.contains(&f.index))
        .map(|f| FunctionInput {
            index: f.index,
            export: f.export_name.as_deref(),
            ops: &f.ops,
        })
        .collect();
    if inputs.len() != shipped.len() {
        bail!(
            "--emit-memory-facts (#1145): the object defines {} func_N bodies and the \
             module has {} of them — refusing to describe an object the module does \
             not match",
            shipped.len(),
            inputs.len()
        );
    }
    for f in &inputs {
        if let Some(e) = f.export
            && !syms.contains_key(e)
        {
            bail!(
                "--emit-memory-facts (#1145): export `{e}` (function {}) is not a symbol \
                 of the object",
                f.index
            );
        }
    }
    let import_names: Vec<String> = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, synth_core::wasm_decoder::ImportKind::Function(_)))
        .map(|i| format!("{}.{}", i.module, i.name))
        .collect();
    let functions = memory_facts::derive(&inputs, &import_names, memory_count, &domains);

    // Cross-check: a relocation inside func_N's own code that names memory
    // k's base or size symbol (k >= 1) means that code ACCESSES memory k —
    // a memory-k pointer is a wasm offset, so those symbols are referenced
    // only at access sites and by memory k's `software` guard. Memory 0 is
    // not checkable this way: on the plain path it is R11-relative (no
    // relocation), and under --native-pointer-abi a relocation against its
    // statics (`__synth_wasm_data`, `__synth_wasm_seg_K`) can FORM a native
    // pointer a callee dereferences — an address, not an access (measured:
    // the #1145 NPA `pages` fixture's `via_call` passes one to `$h0`).
    // Memory 0 is covered by the execution oracle instead.
    if let Some(text) = obj.section_by_name(".text") {
        let ranges: Vec<(u64, u64, u32)> = shipped
            .iter()
            .filter_map(|i| {
                let s = syms.get(&format!("func_{i}"))?;
                (s.section == Some(text.index())).then(|| {
                    let lo = s.value & !1;
                    (lo, lo + s.size, *i)
                })
            })
            .collect();
        for (off, rel) in text.relocations() {
            let RelocationTarget::Symbol(si) = rel.target() else {
                continue;
            };
            let Some(name) = sym_names.get(&si.0) else {
                continue;
            };
            let Some(&k) = mem_of_symbol.get(name) else {
                continue;
            };
            let Some(&(_, _, fi)) = ranges.iter().find(|(lo, hi, _)| *lo <= off && off < *hi)
            else {
                continue;
            };
            let f = functions
                .iter()
                .find(|f| f.index == fi)
                .expect("every shipped function has facts");
            if !f.direct_memories.contains(&k) {
                bail!(
                    "--emit-memory-facts (#1145): func_{fi}'s own code relocates against \
                     `{name}` (memory {k}) but its derived direct memory set is {:?} — \
                     the derivation and the object disagree; refusing to write facts",
                    f.direct_memories
                );
            }
        }
    }

    let report = MemoryFactsReport {
        schema: MEMORY_FACTS_SCHEMA.to_string(),
        object_sha256: synth_core::proven_safe::hex_sha256(&obj_bytes),
        target: target.to_string(),
        memory_count,
        mpu_layout: layout.map(|l| l.as_str().to_string()),
        domains: domains
            .domains
            .iter()
            .map(|(n, m)| (n.clone(), m.iter().copied().collect()))
            .collect(),
        memories,
        functions,
        not_covered: memory_facts::not_covered(),
    };
    let path = sidecar_path(output);
    let json = serde_json::to_string_pretty(&report)? + "\n";
    std::fs::write(&path, json).with_context(|| format!("writing {}", path.display()))?;
    let multi = report
        .functions
        .iter()
        .filter(|f| f.direct_multi_memory)
        .count();
    let spans = report
        .functions
        .iter()
        .filter(|f| f.direct_spans_domains)
        .count();
    println!(
        "  Memory facts: wrote {} ({} functions, {} accessing several memories \
         themselves, {} spanning domains themselves) — {MEMORY_FACTS_SCHEMA}",
        path.display(),
        report.functions.len(),
        multi,
        spans
    );
    Ok(path)
}
