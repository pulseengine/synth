//! RQ-91-MPUENFORCE (#1145): linear-memory ACCESS FACTS for an embedder that
//! programs the MPU itself.
//!
//! synth emits no MPU programming on any path, and on #1145 gale (the
//! embedder) chose to keep it that way: its verified `switch_to_partition`
//! and `gust:mpu/regs` stay the ONLY MPU writer, because synth is build-time
//! and outside the flight TCB. What synth contributes is FACTS, as data,
//! which gale's own build-time gate consumes to prove that each domain's grant
//! is SUFFICIENT (no legitimate access faults) and MINIMAL. Nothing in this
//! module executes on target and nothing here encodes an MPU register.
//!
//! This module is the pure half: from the decoded wasm function bodies it
//! derives, per function, the set of linear memories the body ACCESSES
//! (loads, stores, `memory.fill`, both sides of `memory.copy`) and the
//! TRANSITIVE set over the direct call graph. The memory index of every one
//! of those operators is a static immediate in wasm, so the direct set is
//! exact, not an estimate. Two things widen it, and both are stated in the
//! report rather than folded in silently:
//!
//! * `call_indirect` — the callee is not statically known, so a function that
//!   (transitively) reaches one is given EVERY memory of the module and
//!   carries `via_call_indirect: true`.
//! * a call to an IMPORTED function — host code synth did not emit. Its
//!   accesses are the embedder's own; the report lists the import by name in
//!   `imports_called` and adds no memory for it.
//!
//! `memory.size` and `memory.grow` are NOT accesses: on this backend both
//! lower to constants (every memory is fixed, `memory.grow` returns -1), and
//! neither touches a byte of the memory, so neither needs a grant.
//!
//! The derivation is checked against the shipped object by EXECUTION, not by
//! re-reading this code: `scripts/repro/memory_facts_1145_differential.py`
//! runs every multi-memory fixture under unicorn, attributes every data
//! access to the function whose code issued it, and requires the accessed
//! memory to be in that function's emitted set.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::proven_safe::access_width;
use crate::wasm_op::WasmOp;

/// The sidecar's schema tag.
pub const MEMORY_FACTS_SCHEMA: &str = "synth-memfacts-v1";

/// The memories one operator ACCESSES. Empty for every non-access operator.
///
/// Memory 0's load/store/bulk forms are the bare variants; every non-default
/// memory arrives wrapped in [`WasmOp::MultiMemory`] (decoder-enforced:
/// `memory > 0`, never nested). Load/store classification is
/// [`access_width`], the same predicate the bounds-elision ingest uses, so
/// there is one list of "this operator touches linear memory", not two.
pub fn op_accesses(op: &WasmOp) -> Vec<u32> {
    match op {
        WasmOp::MultiMemory { memory, op } => match op.as_ref() {
            WasmOp::MemoryCopyBetween { dst_mem, src_mem } => {
                let mut v = vec![*dst_mem, *src_mem];
                v.sort_unstable();
                v.dedup();
                v
            }
            inner if access_width(inner).is_some() => vec![*memory],
            WasmOp::MemoryFill | WasmOp::MemoryCopy => vec![*memory],
            // Any other wrapped form is an operator this module does not know
            // to be an access. Attribute it to the wrapped memory anyway:
            // over-granting is the safe direction for a SUFFICIENCY fact, and
            // the execution oracle would show a missed access as a red.
            _ => vec![*memory],
        },
        WasmOp::MemoryCopyBetween { dst_mem, src_mem } => {
            let mut v = vec![*dst_mem, *src_mem];
            v.sort_unstable();
            v.dedup();
            v
        }
        WasmOp::MemoryFill | WasmOp::MemoryCopy => vec![0],
        op if access_width(op).is_some() => vec![0],
        _ => Vec::new(),
    }
}

/// One defined function's own body, before closure.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DirectFacts {
    /// Memories this body accesses itself.
    pub memories: BTreeSet<u32>,
    /// Direct-call targets (module function indices, imports included).
    pub calls: BTreeSet<u32>,
    /// The body contains a `call_indirect`.
    pub call_indirect: bool,
}

/// Scan one function body.
pub fn direct_facts(ops: &[WasmOp]) -> DirectFacts {
    let mut d = DirectFacts::default();
    for op in ops {
        d.memories.extend(op_accesses(op));
        match op {
            WasmOp::Call(f) => {
                d.calls.insert(*f);
            }
            WasmOp::CallIndirect { .. } => d.call_indirect = true,
            _ => {}
        }
    }
    d
}

/// One defined function, as the derivation needs it.
#[derive(Debug, Clone)]
pub struct FunctionInput<'a> {
    /// Module function index (imports counted first).
    pub index: u32,
    /// Export name, if exported.
    pub export: Option<&'a str>,
    /// The decoded body.
    pub ops: &'a [WasmOp],
    /// Module-relative wasm byte offset of each op (same index), or empty
    /// when the decoder recorded none.
    pub op_offsets: &'a [u32],
}

/// The memory-to-domain mapping the embedder supplies. A meld `--domain`
/// maps one-to-one onto a memory index today; nothing here assumes that, so a
/// domain may own several memories. Each memory belongs to at most one domain.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DomainMap {
    /// Domain name -> the memories it owns.
    pub domains: BTreeMap<String, BTreeSet<u32>>,
}

impl DomainMap {
    /// Parse `NAME=K[,K...]` specs. Refuses an empty name, an unparsable or
    /// out-of-range index, a repeated name, a memory claimed by two domains,
    /// and a map that leaves any memory of the module without a domain (a
    /// memory with no domain cannot be granted to anyone, so a gate built on
    /// the map would be silently incomplete).
    pub fn parse(specs: &[String], memory_count: u32) -> Result<Self, String> {
        let mut map = DomainMap::default();
        let mut owner: BTreeMap<u32, String> = BTreeMap::new();
        for spec in specs {
            let (name, list) = spec.split_once('=').ok_or_else(|| {
                format!("--memory-domain {spec:?}: expected NAME=MEMORY[,MEMORY...]")
            })?;
            let name = name.trim();
            if name.is_empty() {
                return Err(format!(
                    "--memory-domain {spec:?}: the domain name is empty"
                ));
            }
            if map.domains.contains_key(name) {
                return Err(format!("--memory-domain: domain {name:?} is given twice"));
            }
            let mut mems = BTreeSet::new();
            for part in list.split(',') {
                let k: u32 = part.trim().parse().map_err(|_| {
                    format!("--memory-domain {spec:?}: {part:?} is not a memory index")
                })?;
                if k >= memory_count {
                    return Err(format!(
                        "--memory-domain {spec:?}: memory {k} does not exist (the module \
                         has {memory_count} memories)"
                    ));
                }
                if let Some(prev) = owner.insert(k, name.to_string()) {
                    return Err(format!(
                        "--memory-domain: memory {k} is claimed by both {prev:?} and {name:?}"
                    ));
                }
                mems.insert(k);
            }
            map.domains.insert(name.to_string(), mems);
        }
        if !map.domains.is_empty() {
            let missing: Vec<u32> = (0..memory_count)
                .filter(|k| !owner.contains_key(k))
                .collect();
            if !missing.is_empty() {
                return Err(format!(
                    "--memory-domain: memories {missing:?} belong to no domain. A memory \
                     with no domain cannot be granted to any execution context, so the \
                     facts would be incomplete; name a domain for every memory"
                ));
            }
        }
        Ok(map)
    }

    /// The domain that owns memory `k`.
    pub fn domain_of(&self, k: u32) -> Option<&str> {
        self.domains
            .iter()
            .find(|(_, m)| m.contains(&k))
            .map(|(n, _)| n.as_str())
    }
}

/// The per-function answer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionFacts {
    /// Module function index.
    pub index: u32,
    /// The object symbol of the body (`func_<index>`).
    pub symbol: String,
    /// Export name, if exported.
    pub export: Option<String>,
    /// Memories the body accesses itself.
    pub direct_memories: Vec<u32>,
    /// The body's direct callees: `func_<N>` for a defined function, the
    /// `module.field` name for an import. With `direct_memories` this is the
    /// call graph, so a consumer can place a context switch at any edge.
    /// Call sites, with their domains, are in the report's
    /// `cross_domain_edges`.
    pub direct_calls: Vec<String>,
    /// `direct_memories` holds more than one memory: this body itself
    /// touches several (a cross-memory adapter, typically).
    pub direct_multi_memory: bool,
    /// The domains of `direct_memories`, when a domain map was given.
    pub direct_domains: Vec<String>,
    /// ROLE: the key for the SUPERVISOR-ONLY ASSERTION. `direct_domains`
    /// holds more than one domain: this body itself touches memories of
    /// several domains, so it is an adapter and can run only in a context
    /// granted all of them (supervisor code), wherever its callers run.
    pub direct_spans_domains: bool,
    /// The domains this function SITS IN, which decides whether a call out of
    /// it crosses: the domains of `direct_memories` when the body touches a
    /// memory; for a body that touches none, the union of its callers'
    /// (it runs in its caller's context); `[]` for such a body nothing calls.
    pub sits_in_domains: Vec<String>,
    /// Memories the body and everything it can call accesses. This is the
    /// grant a context running this function needs if no context switch
    /// happens below it.
    pub memories: Vec<u32>,
    /// `memories` was widened to every memory because a `call_indirect` is
    /// reachable from this function.
    pub via_call_indirect: bool,
    /// This body itself contains a `call_indirect` (treated as reaching every
    /// domain; listed in `cross_domain_edges` when that crosses).
    pub direct_call_indirect: bool,
    /// Imported (host) functions reachable by direct call. Their accesses are
    /// not in `memories`.
    pub imports_called: Vec<String>,
    /// `memories` holds more than one memory (the transitive reading).
    pub multi_memory: bool,
    /// The domains of `memories`, when a domain map was given.
    pub domains: Vec<String>,
    /// ROLE: the key for the REACHABILITY / BOUNDARY CENSUS. `domains` holds
    /// more than one domain: this function's call tree reaches memories of
    /// several domains. A tenant entry that calls a supervisor adapter is
    /// `true` here — a TRUE finding (the tenant can reach supervisor memory
    /// through that call), and the crossing that makes it so is listed in
    /// `cross_domain_edges` — and `false` in `direct_spans_domains`.
    pub spans_domains: bool,
}

/// Derive every defined function's facts.
///
/// `import_names[i]` names imported function `i` (`module.field`);
/// `memory_count` is the size of the module's memory index space.
pub fn derive(
    funcs: &[FunctionInput<'_>],
    import_names: &[String],
    memory_count: u32,
    domains: &DomainMap,
) -> Vec<FunctionFacts> {
    let direct: BTreeMap<u32, DirectFacts> = funcs
        .iter()
        .map(|f| (f.index, direct_facts(f.ops)))
        .collect();
    let num_imports = import_names.len() as u32;
    let all: BTreeSet<u32> = (0..memory_count).collect();

    // Fixpoint over the direct call graph (recursion-safe): a function's
    // closure is its own accesses plus every callee's closure.
    let mut mems: BTreeMap<u32, BTreeSet<u32>> = direct
        .iter()
        .map(|(i, d)| (*i, d.memories.clone()))
        .collect();
    let mut indirect: BTreeMap<u32, bool> =
        direct.iter().map(|(i, d)| (*i, d.call_indirect)).collect();
    let mut imports: BTreeMap<u32, BTreeSet<u32>> = direct
        .iter()
        .map(|(i, d)| {
            (
                *i,
                d.calls
                    .iter()
                    .copied()
                    .filter(|c| *c < num_imports)
                    .collect(),
            )
        })
        .collect();
    loop {
        let mut changed = false;
        for (i, d) in &direct {
            for c in &d.calls {
                if *c < num_imports || !direct.contains_key(c) {
                    continue;
                }
                let (cm, ci, cimp) = (mems[c].clone(), indirect[c], imports[c].clone());
                let m = mems
                    .get_mut(i)
                    .expect("every defined function has an entry");
                let before = m.len();
                m.extend(cm);
                changed |= m.len() != before;
                if ci && !indirect[i] {
                    indirect.insert(*i, true);
                    changed = true;
                }
                let imp = imports.get_mut(i).expect("entry");
                let before = imp.len();
                imp.extend(cimp);
                changed |= imp.len() != before;
            }
        }
        if !changed {
            break;
        }
    }

    let mut facts = funcs
        .iter()
        .map(|f| {
            let via = indirect[&f.index];
            let set: BTreeSet<u32> = if via {
                all.clone()
            } else {
                mems[&f.index].clone()
            };
            let doms_of = |s: &BTreeSet<u32>| -> BTreeSet<String> {
                s.iter()
                    .filter_map(|k| domains.domain_of(*k).map(str::to_string))
                    .collect()
            };
            let doms = doms_of(&set);
            let d = &direct[&f.index];
            let ddoms = doms_of(&d.memories);
            FunctionFacts {
                index: f.index,
                symbol: format!("func_{}", f.index),
                export: f.export.map(str::to_string),
                direct_memories: d.memories.iter().copied().collect(),
                direct_calls: d
                    .calls
                    .iter()
                    .map(|c| match import_names.get(*c as usize) {
                        Some(n) if *c < num_imports => n.clone(),
                        _ => format!("func_{c}"),
                    })
                    .collect(),
                direct_multi_memory: d.memories.len() > 1,
                direct_spans_domains: ddoms.len() > 1,
                sits_in_domains: ddoms.iter().cloned().collect(),
                direct_domains: ddoms.into_iter().collect(),
                memories: set.iter().copied().collect(),
                via_call_indirect: via,
                direct_call_indirect: d.call_indirect,
                imports_called: imports[&f.index]
                    .iter()
                    .map(|i| import_names[*i as usize].clone())
                    .collect(),
                multi_memory: set.len() > 1,
                spans_domains: doms.len() > 1,
                domains: doms.into_iter().collect(),
            }
        })
        .collect::<Vec<_>>();

    // A body that touches no memory runs in its callers' context: it sits
    // in the union of their domains (fixpoint, recursion-safe).
    let pos: BTreeMap<u32, usize> = facts
        .iter()
        .enumerate()
        .map(|(i, f)| (f.index, i))
        .collect();
    loop {
        let mut changed = false;
        for (caller, d) in &direct {
            let from: Vec<String> = facts[pos[caller]].sits_in_domains.clone();
            for c in &d.calls {
                let Some(&ci) = pos.get(c) else { continue };
                if !direct[c].memories.is_empty() {
                    continue;
                }
                let s = &mut facts[ci].sits_in_domains;
                for dom in &from {
                    if !s.contains(dom) {
                        s.push(dom.clone());
                        changed = true;
                    }
                }
                s.sort();
            }
        }
        if !changed {
            break;
        }
    }
    facts
}

/// Where a memory's base address comes from. Never a number: the base is a
/// link-time or run-time quantity the embedder resolves.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum BaseSource {
    /// The linked address of `symbol`, offset 0 of `section`.
    Symbol { symbol: String, section: String },
    /// The value the embedder loads into `register` before any export runs.
    Register { register: String },
    /// `--native-pointer-abi` memory 0: every access is a NATIVE address
    /// (R11 = 0), so the memory is wherever the embedder allocated it. Its
    /// statics, when the module has any, live in `statics_symbol`'s
    /// reservation in `statics_section`; the embedder's region must cover
    /// those and every native pointer it hands in.
    Native {
        statics_symbol: Option<String>,
        statics_section: Option<String>,
    },
}

/// One memory's bounds, read back from the written object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryBounds {
    pub index: u32,
    /// The memory is imported (the embedder supplies it).
    pub imported: bool,
    /// Declared initial size in bytes, exact for the life of the process.
    pub size_bytes: u32,
    /// The symbol `size_bytes` was read from.
    pub size_symbol: String,
    pub base: BaseSource,
    /// `sh_addralign` of the memory's own section, when synth places one.
    pub section_align: Option<u32>,
    /// `sh_size` of that section: equal to `size_bytes` unless a
    /// `--mpu-layout` padded it.
    pub section_bytes: Option<u32>,
    /// The smallest PMSAv7-legal region covering the memory (power of two,
    /// at least 32 B). A PMSAv7 base must be aligned to this.
    pub pmsav7_region_bytes: u32,
    /// The symbol `pmsav7_region_bytes` was read from.
    pub region_symbol: String,
    /// When the section is padded to a subregion granule
    /// (`--mpu-layout pmsav7-srd`) and does not fill its region: how many of
    /// the region's 8 subregions, counted from the base, the section covers.
    /// The embedder disables the rest. `None` otherwise.
    pub pmsav7_subregions_enabled: Option<u32>,
    /// The PMSAv8 granule: base and limit on 32 B; any size is legal.
    pub pmsav8_granule_bytes: u32,
    /// The domain that owns this memory, when a domain map was given.
    pub domain: Option<String>,
}

/// The whole sidecar.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryFactsReport {
    pub schema: String,
    /// sha256 of the object these facts describe, so a stale sidecar is
    /// detectable.
    pub object_sha256: String,
    pub target: String,
    pub memory_count: u32,
    /// `--mpu-layout`, when one was applied.
    pub mpu_layout: Option<String>,
    pub domains: BTreeMap<String, Vec<u32>>,
    pub memories: Vec<MemoryBounds>,
    pub functions: Vec<FunctionFacts>,
    /// One entry per call site that crosses a domain boundary (empty without
    /// a domain map). See [`CallEdge`].
    pub cross_domain_edges: Vec<CallEdge>,
    /// The role of each reading, carried in the sidecar so a consumer reads
    /// the right key for the right check.
    pub field_roles: BTreeMap<String, String>,
    /// What these facts do not cover.
    pub not_covered: Vec<String>,
}

/// The `field_roles` map.
pub fn field_roles() -> BTreeMap<String, String> {
    [
        (
            "direct_spans_domains",
            "SUPERVISOR-ONLY ASSERTION key: the function's OWN body touches memories of \
             more than one domain, so it is an adapter and must be supervisor code",
        ),
        (
            "spans_domains",
            "REACHABILITY / BOUNDARY CENSUS key: the function's call tree reaches \
             memories of more than one domain; for a tenant entry that is a true \
             finding, and the crossing responsible is in cross_domain_edges",
        ),
        (
            "cross_domain_edges",
            "the call sites where the call tree leaves the caller's domains: cutting \
             exactly these edges leaves every function's reach inside sits_in_domains",
        ),
        (
            "memories",
            "the grant a context running the function needs if no context switch \
             happens below it (transitive over direct calls; call_indirect = every memory)",
        ),
        (
            "direct_memories",
            "the memories the function's own body accesses",
        ),
        (
            "sits_in_domains",
            "the domains the function runs in: its own body's, or its callers' when the \
             body touches no memory",
        ),
    ]
    .iter()
    .map(|(k, v)| (k.to_string(), v.to_string()))
    .collect()
}

/// What a call site calls.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum CallKind {
    /// A direct call to a function this module defines.
    Direct,
    /// A direct call to an imported (host) function. It leaves the module,
    /// so it is ALWAYS reported; its memory accesses are the embedder's, so
    /// its `callee_domains` is empty.
    Import,
    /// `call_indirect`: the callee is not statically known, so it is treated
    /// as reaching EVERY domain, as the memory sets treat it.
    CallIndirect,
}

/// Where a call is.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallSite {
    /// The calling function's module index.
    pub function_index: u32,
    /// Index of the call op in the decoded body.
    pub op_index: u32,
    /// Module-relative wasm byte offset of the call op, when known.
    pub wasm_offset: Option<u32>,
}

/// One call site that crosses a domain boundary: the callee's call tree
/// reaches a domain the caller does not sit in (or the callee is an import).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallEdge {
    pub kind: CallKind,
    /// `func_<N>` of the caller.
    pub caller: String,
    /// The caller's export name, if any.
    pub caller_export: Option<String>,
    /// `func_<N>`, the import's `module.field`, or `call_indirect`.
    pub callee: String,
    pub site: CallSite,
    /// The caller's `sits_in_domains`.
    pub caller_domains: Vec<String>,
    /// The callee's transitive `domains` (every domain for `call_indirect`,
    /// none for an import).
    pub callee_domains: Vec<String>,
}

/// Every crossing call site. Empty when `domains` is empty.
pub fn cross_domain_edges(
    funcs: &[FunctionInput<'_>],
    facts: &[FunctionFacts],
    import_names: &[String],
    domains: &DomainMap,
) -> Vec<CallEdge> {
    if domains.domains.is_empty() {
        return Vec::new();
    }
    let by: BTreeMap<u32, &FunctionFacts> = facts.iter().map(|f| (f.index, f)).collect();
    let all: BTreeSet<String> = domains.domains.keys().cloned().collect();
    let sits: BTreeMap<u32, BTreeSet<String>> = facts
        .iter()
        .map(|f| (f.index, f.sits_in_domains.iter().cloned().collect()))
        .collect();
    let num_imports = import_names.len() as u32;
    let mut out = Vec::new();
    for f in funcs {
        let caller = by[&f.index];
        let mine = &sits[&f.index];
        for (i, op) in f.ops.iter().enumerate() {
            let (kind, callee, theirs): (CallKind, String, BTreeSet<String>) = match op {
                WasmOp::Call(c) if *c < num_imports => (
                    CallKind::Import,
                    import_names[*c as usize].clone(),
                    BTreeSet::new(),
                ),
                WasmOp::Call(c) => match by.get(c) {
                    Some(g) => (
                        CallKind::Direct,
                        g.symbol.clone(),
                        g.domains.iter().cloned().collect(),
                    ),
                    None => continue,
                },
                WasmOp::CallIndirect { .. } => (
                    CallKind::CallIndirect,
                    "call_indirect".to_string(),
                    all.clone(),
                ),
                _ => continue,
            };
            let crosses = kind == CallKind::Import || !theirs.is_subset(mine);
            if !crosses {
                continue;
            }
            out.push(CallEdge {
                kind,
                caller: caller.symbol.clone(),
                caller_export: caller.export.clone(),
                callee,
                site: CallSite {
                    function_index: f.index,
                    op_index: i as u32,
                    wasm_offset: f.op_offsets.get(i).copied(),
                },
                caller_domains: mine.iter().cloned().collect(),
                callee_domains: theirs.into_iter().collect(),
            });
        }
    }
    out
}

/// The fixed list of what the facts do not cover, carried in every sidecar so
/// a consumer cannot read the facts as a containment claim.
pub fn not_covered() -> Vec<String> {
    [
        "accesses by imported (host) functions: listed in imports_called, not in memories",
        "the globals table, the stack, literal pools and .text: every context needs \
         them and they are not wasm memories",
        "out-of-bounds accesses: a set says which memories a function touches \
         legitimately; an out-of-bounds address of memory k can land in any memory",
        "an MPU fault is not a wasm trap: under --safety-bounds none or mpu an \
         out-of-bounds bulk op writes in-region bytes before it faults; only \
         --safety-bounds software traps before writing",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect()
}

/// `--mpu-layout`: an opt-in placement of every synth-placed memory section
/// (memory k >= 1, `.synth.wasm_mem_k`) as a legal PMSAv7 region.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MpuLayout {
    /// Pad the section to its whole power-of-two region, so the region the
    /// embedder programs covers this memory and nothing else.
    Pmsav7,
    /// Pad only to the region's subregion granule (region / 8, regions of at
    /// least 256 B), so ONE region with its top subregions disabled covers
    /// exactly the padded section. Regions under 256 B have no subregions and
    /// are padded whole, as under [`MpuLayout::Pmsav7`].
    Pmsav7Srd,
}

impl MpuLayout {
    /// Parse the flag value.
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "pmsav7" => Ok(MpuLayout::Pmsav7),
            "pmsav7-srd" => Ok(MpuLayout::Pmsav7Srd),
            other => Err(format!(
                "--mpu-layout {other:?}: expected `pmsav7` (pad each memory to its \
                 power-of-two region) or `pmsav7-srd` (pad to the region's subregion \
                 granule)"
            )),
        }
    }

    /// The flag value, as recorded in the sidecar.
    pub fn as_str(&self) -> &'static str {
        match self {
            MpuLayout::Pmsav7 => "pmsav7",
            MpuLayout::Pmsav7Srd => "pmsav7-srd",
        }
    }
}

/// The smallest PMSAv7 region that has subregions.
pub const PMSAV7_SRD_MIN_REGION: u32 = 256;

/// Where a placed memory section ends up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Placement {
    /// `sh_addralign`: the region size, so the base is region-aligned.
    pub align: u32,
    /// `sh_size`: the declared size padded per the layout.
    pub section_bytes: u32,
}

/// Lay out one memory section of `declared` bytes whose PMSAv7 region is
/// `region` and whose v0.68 section alignment is `align` (both computed by
/// the builder, so this function adds padding and nothing else).
///
/// Refuses, with the reason, when the memory cannot be one PMSAv7 region:
/// a region the builder saturated (a declaration above 2^31 B has no
/// power-of-two in u32), or an alignment that differs from the region (the
/// v0.68 alignment is capped at 2^31).
pub fn place(
    mem_idx: u32,
    declared: u32,
    region: u32,
    align: u32,
    layout: MpuLayout,
) -> Result<Placement, String> {
    if !region.is_power_of_two() || region < declared || align != region {
        return Err(format!(
            "--mpu-layout {} (#1145): memory {mem_idx} ({declared} B) cannot be laid \
             out as one PMSAv7 region: its region would be {region} B with section \
             alignment {align} B, and a PMSAv7 region is a power of two of at most \
             2^31 B whose base is aligned to its size. Refusing rather than emitting \
             a section no single region can cover",
            layout.as_str()
        ));
    }
    let section_bytes = match layout {
        MpuLayout::Pmsav7 => region,
        MpuLayout::Pmsav7Srd if region < PMSAV7_SRD_MIN_REGION => region,
        MpuLayout::Pmsav7Srd => {
            let granule = region / 8;
            declared.div_ceil(granule).max(1) * granule
        }
    };
    Ok(Placement {
        align,
        section_bytes,
    })
}

/// The number of low PMSAv7 subregions (of 8) a region of `region` bytes
/// needs enabled to cover `section_bytes`, or `None` when the region has no
/// subregions (< 256 B) or the section fills it.
pub fn subregions_enabled(section_bytes: u32, region: u32) -> Option<u32> {
    if region < PMSAV7_SRD_MIN_REGION || !region.is_power_of_two() || section_bytes >= region {
        return None;
    }
    Some(section_bytes.div_ceil(region / 8))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mm(k: u32, op: WasmOp) -> WasmOp {
        WasmOp::MultiMemory {
            memory: k,
            op: Box::new(op),
        }
    }

    #[test]
    fn op_accesses_classifies_every_memory_form() {
        let ld = WasmOp::I32Load8U {
            offset: 0,
            align: 0,
        };
        assert_eq!(op_accesses(&ld), vec![0]);
        assert_eq!(op_accesses(&mm(2, ld.clone())), vec![2]);
        assert_eq!(op_accesses(&WasmOp::MemoryFill), vec![0]);
        assert_eq!(op_accesses(&mm(1, WasmOp::MemoryFill)), vec![1]);
        assert_eq!(
            op_accesses(&mm(
                1,
                WasmOp::MemoryCopyBetween {
                    dst_mem: 0,
                    src_mem: 1
                }
            )),
            vec![0, 1]
        );
        assert!(op_accesses(&WasmOp::MemorySize(1)).is_empty());
        assert!(op_accesses(&WasmOp::MemoryGrow(1)).is_empty());
        assert!(op_accesses(&WasmOp::I32Add).is_empty());
    }

    fn st(k: u32) -> WasmOp {
        let s = WasmOp::I32Store {
            offset: 0,
            align: 2,
        };
        if k == 0 { s } else { mm(k, s) }
    }

    #[test]
    fn closure_follows_calls_and_recursion_and_names_imports() {
        // import 0 = env.log; f1 -> f2 -> f1 (cycle); f2 touches memory 1;
        // f1 touches memory 0 and calls the import; f3 alone touches 2.
        let f1 = vec![st(0), WasmOp::Call(2), WasmOp::Call(0)];
        let f2 = vec![st(1), WasmOp::Call(1)];
        let f3 = vec![st(2)];
        let funcs = [
            FunctionInput {
                index: 1,
                export: Some("a"),
                ops: &f1,
                op_offsets: &[],
            },
            FunctionInput {
                index: 2,
                export: None,
                ops: &f2,
                op_offsets: &[],
            },
            FunctionInput {
                index: 3,
                export: Some("c"),
                ops: &f3,
                op_offsets: &[],
            },
        ];
        let doms = DomainMap::parse(&["t=0".into(), "s=1,2".into()], 3).unwrap();
        let r = derive(&funcs, &["env.log".into()], 3, &doms);
        assert_eq!(r[0].direct_memories, vec![0]);
        assert_eq!(r[0].memories, vec![0, 1]);
        assert_eq!(r[0].imports_called, vec!["env.log".to_string()]);
        assert!(r[0].multi_memory && r[0].spans_domains);
        assert!(!r[0].direct_multi_memory && !r[0].direct_spans_domains);
        assert_eq!(
            r[0].direct_calls,
            vec!["env.log".to_string(), "func_2".to_string()]
        );
        assert_eq!(r[0].direct_domains, vec!["t".to_string()]);
        assert_eq!(r[1].memories, vec![0, 1], "the cycle closes both ways");
        assert_eq!(r[1].imports_called, vec!["env.log".to_string()]);
        assert_eq!(r[2].memories, vec![2]);
        assert!(!r[2].multi_memory && !r[2].spans_domains);
        assert_eq!(r[2].domains, vec!["s".to_string()]);
    }

    #[test]
    fn call_indirect_widens_to_every_memory_and_says_so() {
        let f1 = vec![
            st(1),
            WasmOp::CallIndirect {
                type_index: 0,
                table_index: 0,
            },
        ];
        let f2 = vec![WasmOp::Call(0)];
        let funcs = [
            FunctionInput {
                index: 0,
                export: None,
                ops: &f1,
                op_offsets: &[],
            },
            FunctionInput {
                index: 1,
                export: Some("e"),
                ops: &f2,
                op_offsets: &[],
            },
        ];
        let r = derive(&funcs, &[], 3, &DomainMap::default());
        assert_eq!(r[0].direct_memories, vec![1]);
        assert_eq!(r[0].memories, vec![0, 1, 2]);
        assert!(r[0].via_call_indirect);
        assert_eq!(r[1].memories, vec![0, 1, 2]);
        assert!(r[1].via_call_indirect, "propagates to callers");
        assert!(r[1].domains.is_empty() && !r[1].spans_domains);
    }

    #[test]
    fn place_pads_to_the_region_or_the_subregion_granule() {
        // 3 pages = 192 KiB: region 256 KiB, granule 32 KiB.
        let d = 3 * 65536;
        let r = 1 << 18;
        let p = place(1, d, r, r, MpuLayout::Pmsav7).unwrap();
        assert_eq!((p.align, p.section_bytes), (r, r));
        let s = place(1, d, r, r, MpuLayout::Pmsav7Srd).unwrap();
        assert_eq!((s.align, s.section_bytes), (r, d), "6 granules exactly");
        assert_eq!(subregions_enabled(s.section_bytes, r), Some(6));
        // 5000 B: region 8 KiB, granule 1 KiB -> 5 KiB.
        let s = place(1, 5000, 8192, 8192, MpuLayout::Pmsav7Srd).unwrap();
        assert_eq!(s.section_bytes, 5120);
        assert_eq!(subregions_enabled(5120, 8192), Some(5));
        // Under 256 B there are no subregions: the whole region.
        let s = place(1, 40, 64, 64, MpuLayout::Pmsav7Srd).unwrap();
        assert_eq!(s.section_bytes, 64);
        assert_eq!(subregions_enabled(64, 64), None);
        // A power-of-two declaration is already its region.
        let p = place(1, 65536, 65536, 65536, MpuLayout::Pmsav7).unwrap();
        assert_eq!(p.section_bytes, 65536);
        assert_eq!(subregions_enabled(65536, 65536), None);
    }

    #[test]
    fn place_refuses_what_no_single_region_covers() {
        // The builder saturates the region of a > 2^31 B declaration.
        assert!(place(1, 0x8000_0001, u32::MAX, 1 << 31, MpuLayout::Pmsav7).is_err());
        // Alignment capped below the region.
        assert!(place(1, 100, 128, 64, MpuLayout::Pmsav7).is_err());
        // A region smaller than the declaration.
        assert!(place(1, 100, 64, 64, MpuLayout::Pmsav7Srd).is_err());
        assert!(MpuLayout::parse("pmsav8").is_err());
        assert_eq!(
            MpuLayout::parse("pmsav7-srd").unwrap(),
            MpuLayout::Pmsav7Srd
        );
    }

    /// The adapter shape: tenant entry (memory 0) -> adapter (0 and 1) ->
    /// supervisor helper (1) and a domainless helper; plus a domainless
    /// entry calling the tenant, an import call and a call_indirect.
    #[test]
    fn cross_domain_edges_are_exactly_where_the_reach_leaves_the_domain() {
        let helper = vec![WasmOp::I32Const(1), WasmOp::Drop]; // touches nothing
        let sup = vec![st(1)];
        let adapter = vec![st(0), st(1), WasmOp::Call(1), WasmOp::Call(2)];
        let tenant = vec![st(0), WasmOp::Call(3), WasmOp::Call(0)];
        let entry = vec![WasmOp::Call(4)];
        let ind = vec![
            st(0),
            WasmOp::CallIndirect {
                type_index: 0,
                table_index: 0,
            },
        ];
        let offs = [10u32, 11, 12];
        fn fi<'a>(
            index: u32,
            export: Option<&'a str>,
            ops: &'a [WasmOp],
            op_offsets: &'a [u32],
        ) -> FunctionInput<'a> {
            FunctionInput {
                index,
                export,
                ops,
                op_offsets,
            }
        }
        // import 0 = env.log; defined 1.. : helper 1, sup 2, adapter 3, tenant 4, entry 5, ind 6
        let funcs = [
            fi(1, None, &helper, &[]),
            fi(2, None, &sup, &[]),
            fi(3, None, &adapter, &[]),
            fi(4, Some("tenant"), &tenant, &offs),
            fi(5, Some("entry"), &entry, &[]),
            fi(6, Some("ind"), &ind, &[]),
        ];
        let doms = DomainMap::parse(&["t=0".into(), "s=1".into()], 2).unwrap();
        let names = vec!["env.log".to_string()];
        let facts = derive(&funcs, &names, 2, &doms);
        let sits = |i: usize| facts[i].sits_in_domains.clone();
        assert_eq!(
            sits(0),
            vec!["s".to_string(), "t".to_string()],
            "helper inherits the adapter's"
        );
        assert_eq!(
            sits(4),
            Vec::<String>::new(),
            "a domainless entry nothing calls"
        );
        let edges = cross_domain_edges(&funcs, &facts, &names, &doms);
        let got: Vec<(String, String, CallKind, u32, Option<u32>)> = edges
            .iter()
            .map(|e| {
                (
                    e.caller.clone(),
                    e.callee.clone(),
                    e.kind.clone(),
                    e.site.op_index,
                    e.site.wasm_offset,
                )
            })
            .collect();
        assert_eq!(
            got,
            vec![
                (
                    "func_4".into(),
                    "func_3".into(),
                    CallKind::Direct,
                    1,
                    Some(11)
                ),
                (
                    "func_4".into(),
                    "env.log".into(),
                    CallKind::Import,
                    2,
                    Some(12)
                ),
                ("func_5".into(), "func_4".into(), CallKind::Direct, 0, None),
                (
                    "func_6".into(),
                    "call_indirect".into(),
                    CallKind::CallIndirect,
                    1,
                    None
                ),
            ]
        );
        assert_eq!(edges[0].caller_domains, vec!["t".to_string()]);
        assert_eq!(
            edges[0].callee_domains,
            vec!["s".to_string(), "t".to_string()]
        );
        assert!(cross_domain_edges(&funcs, &facts, &names, &DomainMap::default()).is_empty());
    }

    #[test]
    fn domain_map_refuses_every_ambiguous_shape() {
        assert!(DomainMap::parse(&["a=0".into(), "b=0".into()], 2).is_err());
        assert!(DomainMap::parse(&["a=0".into(), "a=1".into()], 2).is_err());
        assert!(DomainMap::parse(&["a=2".into()], 2).is_err());
        assert!(DomainMap::parse(&["a=x".into()], 2).is_err());
        assert!(DomainMap::parse(&["=0".into()], 2).is_err());
        assert!(DomainMap::parse(&["a0".into()], 2).is_err());
        assert!(
            DomainMap::parse(&["a=0".into()], 2).is_err(),
            "memory 1 unowned"
        );
        let m = DomainMap::parse(&["a=0".into(), "b=1".into()], 2).unwrap();
        assert_eq!(m.domain_of(1), Some("b"));
        assert_eq!(DomainMap::parse(&[], 2).unwrap(), DomainMap::default());
    }
}
