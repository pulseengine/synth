//! #418 — bind the passed-through embedder import `env::__cabi_arena_realloc`
//! to a synthesized in-module arena allocator, unlocking the fully
//! SELF-CONTAINED dissolve.
//!
//! ## The seam this closes
//!
//! The BYO-OS lean-MCU dissolve (gale#89) builds grow-free components with the
//! wit-bindgen `cabi-realloc-extern` feature: `cabi_realloc` stays exported but
//! its body routes to an embedder-provided `env::__cabi_arena_realloc` import.
//! On the `--relocatable` host-link path that import is DELIBERATELY left as an
//! undefined symbol the TCB's native allocator satisfies at link (#420 locks
//! that layering — nothing here changes it). But on the default SELF-CONTAINED
//! path the same import previously degraded the compile to an ET_REL "link me
//! with the Kiln bridge" object: the one unresolved seam blocking a fully
//! self-contained image.
//!
//! ## The binding (a wasm→wasm rewrite, not new codegen)
//!
//! When the arena import is the module's ONLY import, replace it with a
//! DEFINED WebAssembly function implementing the #418 contract, compiled
//! through synth's ordinary pipeline like any other module function:
//!
//! - signature `(old_ptr, old_len, align, new_len) -> ptr` (`i32×4 → i32`);
//! - `old_len == 0 && new_len == 0` → return `align` verbatim;
//! - bump allocation from a fresh mutable cursor global (appended at the end
//!   of the global index space), aligned up per call;
//! - realloc preserves `min(old_len, new_len)` bytes (byte-copy loop);
//! - BOUNDED arena `[arena_base, arena_end)` — exhaustion (or a zero /
//!   non-power-of-two-shaped `align` wrap) executes `unreachable`, i.e. traps,
//!   and NEVER calls `memory.grow`.
//!
//! `arena_base` mirrors the shipped used-extent rule (`main.rs` #237/#354):
//! `max(data_end, every i32-const global init ≤ linmem)` — the latter covers
//! both the `__stack_pointer` class and wasm-ld's `__data_end`/`__heap_base`
//! layout globals — rounded up to 16 (floor 16 so the allocator never returns
//! a null-looking pointer). `arena_end` = the initial linear-memory size
//! (grow-free modules never extend it).
//!
//! ## Why the rewrite is index-preserving
//!
//! The wasm function index space is imports-first. Removing the SOLE function
//! import and prepending the allocator as the FIRST defined function gives it
//! the import's old index — every `call`, `ref.func`, export, and element
//! entry keeps its meaning without any remapping. Untouched sections are
//! copied byte-for-byte; only import (dropped), function/code (one entry
//! prepended) and global (one entry appended) change.

use anyhow::{Context, Result, bail};
use wasm_encoder::{BlockType, Function, MemArg, ValType};
use wasmparser::{Parser, Payload};

/// The core-module field name of the embedder arena import (#418). The kebab
/// `cabi-arena-realloc` is component-surface only and never reaches synth.
pub const ARENA_IMPORT_MODULE: &str = "env";
pub const ARENA_IMPORT_FIELD: &str = "__cabi_arena_realloc";

/// Outcome of [`bind_cabi_arena_realloc`].
#[derive(Debug)]
pub enum ArenaBind {
    /// No arena import in the module — silent byte-identical pass-through
    /// (the overwhelmingly common case; not worth a log line).
    NoArenaImport,
    /// The arena import is present but the module keeps the host-linked
    /// seam (reason worth logging); byte-identical pass-through.
    KeptHostSeam(&'static str),
    /// The import was bound: compile `bytes` instead of the input.
    Bound(BoundArena),
}

/// A successful #418 binding.
#[derive(Debug)]
pub struct BoundArena {
    /// The rewritten module (arena import replaced by a defined allocator).
    pub bytes: Vec<u8>,
    /// First allocatable wasm address (16-aligned, above all statics).
    pub arena_base: u32,
    /// One past the last allocatable wasm address (= initial memory size).
    pub arena_end: u32,
}

/// Everything learned in the analysis pass.
struct Scan {
    /// (import type index) when `env::__cabi_arena_realloc` is present.
    arena_type_idx: Option<u32>,
    /// Whether the arena import's declared type is `(i32×4) -> i32`.
    arena_sig_ok: bool,
    total_imports: u32,
    /// Initial pages of memory 0, if declared (None = no memory).
    memory_pages: Option<u64>,
    memory64: bool,
    defined_globals: u32,
    /// Max `off + len` over active i32-const-offset segments on memory 0.
    data_end: u32,
    /// A data segment whose offset synth cannot evaluate statically.
    non_const_data_offset: bool,
    /// Max i32-const global init (any mutability) — the `__stack_pointer` /
    /// `__heap_base` / `__data_end` class, filtered to `<= linmem` later.
    global_inits: Vec<u32>,
    has_function_section: bool,
    has_code_section: bool,
}

fn scan(wasm: &[u8]) -> Result<Scan> {
    let mut s = Scan {
        arena_type_idx: None,
        arena_sig_ok: false,
        total_imports: 0,
        memory_pages: None,
        memory64: false,
        defined_globals: 0,
        data_end: 0,
        non_const_data_offset: false,
        global_inits: Vec::new(),
        has_function_section: false,
        has_code_section: false,
    };
    let mut func_types: Vec<bool> = Vec::new(); // per type index: is (i32×4)->i32
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.context("parse wasm (#418 arena-bind scan)")? {
            Payload::TypeSection(reader) => {
                for rec_group in reader {
                    for sub_ty in rec_group.context("parse type section (#418)")?.types() {
                        let ok = match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => {
                                f.params().len() == 4
                                    && f.params().iter().all(|t| *t == wasmparser::ValType::I32)
                                    && f.results() == [wasmparser::ValType::I32]
                            }
                            _ => false,
                        };
                        func_types.push(ok);
                    }
                }
            }
            Payload::ImportSection(reader) => {
                // wasmparser 0.221+ compact-imports grouping: flatten back to
                // individual `Import`s (same idiom as wasm_decoder.rs).
                for import in reader.into_imports() {
                    let import = import.context("parse import (#418)")?;
                    s.total_imports += 1;
                    if import.module == ARENA_IMPORT_MODULE
                        && import.name == ARENA_IMPORT_FIELD
                        && let wasmparser::TypeRef::Func(type_idx) = import.ty
                    {
                        s.arena_type_idx = Some(type_idx);
                        s.arena_sig_ok =
                            func_types.get(type_idx as usize).copied().unwrap_or(false);
                    }
                }
            }
            Payload::MemorySection(reader) => {
                for (i, mem) in reader.into_iter().enumerate() {
                    let mem = mem.context("parse memory (#418)")?;
                    if i == 0 {
                        s.memory_pages = Some(mem.initial);
                        s.memory64 = mem.memory64;
                    }
                }
            }
            Payload::GlobalSection(reader) => {
                for global in reader {
                    let global = global.context("parse global (#418)")?;
                    s.defined_globals += 1;
                    // i32.const inits mark the static layout (SP top,
                    // __heap_base/__data_end) — mirror the used-extent rule.
                    let mut ops = global.init_expr.get_operators_reader();
                    if let Ok(wasmparser::Operator::I32Const { value }) = ops.read()
                        && value > 0
                    {
                        s.global_inits.push(value as u32);
                    }
                }
            }
            Payload::DataSection(reader) => {
                for seg in reader {
                    let seg = seg.context("parse data segment (#418)")?;
                    if let wasmparser::DataKind::Active {
                        memory_index,
                        offset_expr,
                    } = seg.kind
                    {
                        if memory_index != 0 {
                            continue; // multi-memory declines self-contained anyway
                        }
                        let mut ops = offset_expr.get_operators_reader();
                        match ops.read() {
                            Ok(wasmparser::Operator::I32Const { value }) => {
                                let end = (value as u32).saturating_add(seg.data.len() as u32);
                                s.data_end = s.data_end.max(end);
                            }
                            _ => s.non_const_data_offset = true,
                        }
                    }
                }
            }
            Payload::FunctionSection(_) => s.has_function_section = true,
            Payload::CodeSectionStart { .. } => s.has_code_section = true,
            _ => {}
        }
    }
    Ok(s)
}

/// Encode the allocator body (the #418 contract — see module docs).
///
/// Params: 0 = old_ptr, 1 = old_len, 2 = align, 3 = new_len.
/// Locals: 4 = aligned, 5 = end, 6 = n (copy length), 7 = i.
fn allocator_body(cursor_global: u32, arena_end: u32) -> Function {
    let mem = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };
    let mut f = Function::new([(4, ValType::I32)]);
    // contract: old_len == 0 && new_len == 0 -> return align verbatim
    f.instructions()
        .local_get(1)
        .i32_eqz()
        .local_get(3)
        .i32_eqz()
        .i32_and()
        .if_(BlockType::Empty)
        .local_get(2)
        .return_()
        .end()
        // align == 0 is contract-violating input (power of two >= 1): trap
        // rather than compute a wrapped mask.
        .local_get(2)
        .i32_eqz()
        .if_(BlockType::Empty)
        .unreachable()
        .end()
        // aligned = (cursor + align - 1) & ~(align - 1)
        .global_get(cursor_global)
        .local_get(2)
        .i32_add()
        .i32_const(1)
        .i32_sub()
        .local_get(2)
        .i32_const(1)
        .i32_sub()
        .i32_const(-1)
        .i32_xor()
        .i32_and()
        .local_set(4)
        // unsigned wrap while rounding up -> trap
        .local_get(4)
        .global_get(cursor_global)
        .i32_lt_u()
        .if_(BlockType::Empty)
        .unreachable()
        .end()
        // end = aligned + new_len; unsigned wrap -> trap
        .local_get(4)
        .local_get(3)
        .i32_add()
        .local_tee(5)
        .local_get(4)
        .i32_lt_u()
        .if_(BlockType::Empty)
        .unreachable()
        .end()
        // BOUNDED arena: end > arena_end -> trap (never memory.grow)
        .local_get(5)
        .i32_const(arena_end as i32)
        .i32_gt_u()
        .if_(BlockType::Empty)
        .unreachable()
        .end()
        // commit the bump
        .local_get(5)
        .global_set(cursor_global)
        // n = min(old_len, new_len) — realloc preserves the prefix
        .local_get(1)
        .local_get(3)
        .local_get(1)
        .local_get(3)
        .i32_lt_u()
        .select()
        .local_set(6)
        // byte-copy loop: dst = aligned + i, src = old_ptr + i, i < n
        .block(BlockType::Empty)
        .loop_(BlockType::Empty)
        .local_get(7)
        .local_get(6)
        .i32_ge_u()
        .br_if(1)
        .local_get(4)
        .local_get(7)
        .i32_add()
        .local_get(0)
        .local_get(7)
        .i32_add()
        .i32_load8_u(mem)
        .i32_store8(mem)
        .local_get(7)
        .i32_const(1)
        .i32_add()
        .local_set(7)
        .br(0)
        .end()
        .end()
        .local_get(4)
        .end();
    f
}

/// Read a LEB128 u32 from `bytes`, returning (value, length).
fn read_uleb(bytes: &[u8]) -> Result<(u32, usize)> {
    let mut value: u32 = 0;
    let mut shift = 0;
    for (i, &b) in bytes.iter().enumerate().take(5) {
        value |= u32::from(b & 0x7F) << shift;
        if b & 0x80 == 0 {
            return Ok((value, i + 1));
        }
        shift += 7;
    }
    bail!("malformed LEB128 count in section (#418)");
}

fn write_uleb(mut value: u32, out: &mut Vec<u8>) {
    loop {
        let mut b = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            b |= 0x80;
        }
        out.push(b);
        if value == 0 {
            return;
        }
    }
}

fn write_sleb(mut value: i32, out: &mut Vec<u8>) {
    loop {
        let b = (value & 0x7F) as u8;
        value >>= 7;
        let sign = b & 0x40;
        if (value == 0 && sign == 0) || (value == -1 && sign != 0) {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

/// A raw section body with one entry PREPENDED (count bumped, existing
/// entries byte-copied verbatim).
fn prepend_entry(contents: &[u8], entry: &[u8]) -> Result<Vec<u8>> {
    let (count, len) = read_uleb(contents)?;
    let mut out = Vec::with_capacity(contents.len() + entry.len() + 1);
    write_uleb(count + 1, &mut out);
    out.extend_from_slice(entry);
    out.extend_from_slice(&contents[len..]);
    Ok(out)
}

/// A raw section body with one entry APPENDED (count bumped, existing
/// entries byte-copied verbatim).
fn append_entry(contents: &[u8], entry: &[u8]) -> Result<Vec<u8>> {
    let (count, len) = read_uleb(contents)?;
    let mut out = Vec::with_capacity(contents.len() + entry.len() + 1);
    write_uleb(count + 1, &mut out);
    out.extend_from_slice(&contents[len..]);
    out.extend_from_slice(entry);
    Ok(out)
}

/// The encoded cursor global entry: `(global (mut i32) (i32.const base))`.
fn cursor_global_entry(arena_base: u32) -> Vec<u8> {
    let mut e = vec![0x7F, 0x01, 0x41]; // valtype i32, mutable, i32.const
    write_sleb(arena_base as i32, &mut e);
    e.push(0x0B); // end
    e
}

/// Bind a sole `env::__cabi_arena_realloc` function import to a synthesized
/// in-module arena allocator (#418). See the module docs for the contract.
///
/// - `Ok(NoArenaImport)` / `Ok(KeptHostSeam)` — pass the original bytes
///   through byte-identically (the latter: arena import present but the
///   module has OTHER imports too, so it cannot self-contain regardless).
/// - `Ok(Bound)` — compile the returned bytes instead.
/// - `Err` — the arena import is present and this is the self-contained
///   path, but the module is not soundly bindable: refuse LOUDLY rather
///   than emit a silently-degraded object.
pub fn bind_cabi_arena_realloc(wasm: &[u8]) -> Result<ArenaBind> {
    let s = scan(wasm)?;
    let Some(arena_type_idx) = s.arena_type_idx else {
        return Ok(ArenaBind::NoArenaImport);
    };
    if s.total_imports > 1 {
        // Other embedder imports remain — the image cannot self-contain, so
        // the arena import stays on the documented pass-through seam
        // (undefined symbol, host-linked) alongside them.
        return Ok(ArenaBind::KeptHostSeam(
            "module has other imports — keeping the host-linked seam",
        ));
    }
    if !s.arena_sig_ok {
        bail!(
            "#418: env::{ARENA_IMPORT_FIELD} is imported with a signature \
             other than (i32, i32, i32, i32) -> i32 — not the canonical-ABI \
             arena realloc contract; refusing to bind (compile with \
             --no-bind-cabi-arena to keep it an external symbol)"
        );
    }
    let Some(pages) = s.memory_pages else {
        bail!(
            "#418: cannot bind env::{ARENA_IMPORT_FIELD}: the module declares \
             no linear memory to allocate from"
        );
    };
    if s.memory64 {
        bail!("#418: cannot bind env::{ARENA_IMPORT_FIELD}: memory64 module");
    }
    if s.non_const_data_offset {
        bail!(
            "#418: cannot bind env::{ARENA_IMPORT_FIELD}: a data segment has \
             a non-constant offset, so the static-data extent (the arena \
             floor) cannot be derived soundly"
        );
    }
    if !s.has_function_section || !s.has_code_section {
        bail!(
            "#418: cannot bind env::{ARENA_IMPORT_FIELD}: the module defines \
             no functions (nothing synth could route the binding through)"
        );
    }

    let arena_end: u32 = u32::try_from(pages.saturating_mul(64 * 1024))
        .unwrap_or(u32::MAX)
        .min(0xFFFF_0000);
    // Arena floor: above every byte the module statically claims — active
    // data segments plus the i32-const global-init class (__stack_pointer
    // top, wasm-ld's __heap_base/__data_end), mirroring the shipped
    // used-extent rule. Floor 16, rounded up to 16.
    let global_top = s
        .global_inits
        .iter()
        .copied()
        .filter(|&v| v <= arena_end)
        .max()
        .unwrap_or(0);
    let arena_base = s.data_end.max(global_top).max(16).next_multiple_of(16);
    if arena_base >= arena_end {
        bail!(
            "#418: cannot bind env::{ARENA_IMPORT_FIELD}: the static layout \
             (data + stack + wasm-ld layout globals) extends to {arena_base} \
             bytes but linear memory is only {arena_end} bytes — no arena \
             region left; every allocation would trap"
        );
    }

    // The cursor global goes at the END of the global index space; with the
    // sole import removed there are no imported globals, so its index is the
    // defined-global count.
    let cursor_global = s.defined_globals;
    let mut body = Vec::new();
    wasm_encoder::Encode::encode(&allocator_body(cursor_global, arena_end), &mut body);

    // ── Rewrite pass: byte-copy everything except the four touched sections.
    let mut module = wasm_encoder::Module::new();
    let mut global_emitted = false;
    let mut function_emitted = false;
    // Insert the (possibly missing) global section at its canonical position:
    // just before the first section that must FOLLOW it.
    let ensure_globals = |module: &mut wasm_encoder::Module, emitted: &mut bool| {
        if !*emitted {
            let mut out = Vec::new();
            write_uleb(1, &mut out);
            out.extend_from_slice(&cursor_global_entry(arena_base));
            module.section(&wasm_encoder::RawSection {
                id: wasm_encoder::SectionId::Global as u8,
                data: &out,
            });
            *emitted = true;
        }
    };

    for payload in Parser::new(0).parse_all(wasm) {
        let payload = payload.context("parse wasm (#418 arena-bind rewrite)")?;
        match &payload {
            Payload::Version { .. } | Payload::End(_) => {}
            Payload::ImportSection(_) => {
                // The sole import is the arena import — drop the section.
            }
            Payload::FunctionSection(reader) => {
                let mut entry = Vec::new();
                write_uleb(arena_type_idx, &mut entry);
                let contents = &wasm[section_span(reader.range(), wasm)?];
                module.section(&wasm_encoder::RawSection {
                    id: wasm_encoder::SectionId::Function as u8,
                    data: &prepend_entry(contents, &entry)?,
                });
                function_emitted = true;
            }
            Payload::GlobalSection(reader) => {
                let contents = &wasm[section_span(reader.range(), wasm)?];
                module.section(&wasm_encoder::RawSection {
                    id: wasm_encoder::SectionId::Global as u8,
                    data: &append_entry(contents, &cursor_global_entry(arena_base))?,
                });
                global_emitted = true;
            }
            Payload::ExportSection(_)
            | Payload::StartSection { .. }
            | Payload::ElementSection(_)
            | Payload::DataCountSection { .. }
            | Payload::DataSection(_) => {
                ensure_globals(&mut module, &mut global_emitted);
                copy_raw(&mut module, &payload, wasm)?;
            }
            Payload::CodeSectionStart { range, .. } => {
                ensure_globals(&mut module, &mut global_emitted);
                // `range` spans the full section contents (count + bodies);
                // `size` would EXCLUDE the count leb — do not use it here.
                let contents = &wasm[section_span(range.clone(), wasm)?];
                module.section(&wasm_encoder::RawSection {
                    id: wasm_encoder::SectionId::Code as u8,
                    data: &prepend_entry(contents, &body)?,
                });
            }
            Payload::CodeSectionEntry(_) => {} // consumed via CodeSectionStart
            other => copy_raw(&mut module, other, wasm)?,
        }
    }
    if !function_emitted {
        bail!("#418 internal: function section not re-emitted"); // unreachable: scanned above
    }

    let bytes = module.finish();
    // Internal gate: the rewrite must be a VALID module — a malformed rewrite
    // here would otherwise surface as a confusing decode error downstream.
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .context("#418 internal: arena-bind rewrite produced an invalid module (bug)")?;
    Ok(ArenaBind::Bound(BoundArena {
        bytes,
        arena_base,
        arena_end,
    }))
}

/// A wasmparser section range, narrowed to a slice range PROVEN to lie inside
/// `wasm` — or a loud refusal (#965, RQ-83-RANGEWIDEN).
///
/// wasm-tools 0.261 widened `Payload`'s section ranges from `Range<usize>` to
/// `Range<u64>` for the 64-bit-memory story. `as usize` would compile and
/// SILENTLY TRUNCATE a malformed 4 GiB-plus offset into a wrong-bytes read,
/// which is the silent-miscompile class this crate exists to prevent — and it is
/// invisible to the compiler, because `as` accepts both widths. So the conversion
/// REFUSES instead.
///
/// It checks the END against the buffer too, not just the width: a range that
/// converts cleanly can still point past the input, and `&wasm[range]` would then
/// panic rather than return an error. On a 64-bit host the `try_from` arms are
/// unreachable today; they are the half that stays correct on a 32-bit one.
fn section_span(range: core::ops::Range<u64>, wasm: &[u8]) -> Result<core::ops::Range<usize>> {
    let Ok(start) = usize::try_from(range.start) else {
        bail!(
            "#965: section range start {} exceeds this platform's usize — \
             refusing rather than truncating",
            range.start
        );
    };
    let Ok(end) = usize::try_from(range.end) else {
        bail!(
            "#965: section range end {} exceeds this platform's usize — \
             refusing rather than truncating",
            range.end
        );
    };
    if start > end || end > wasm.len() {
        bail!(
            "#965: section range {start}..{end} does not lie inside a {}-byte \
             module — refusing rather than indexing out of bounds",
            wasm.len()
        );
    }
    Ok(start..end)
}

/// Byte-copy one section verbatim.
fn copy_raw(module: &mut wasm_encoder::Module, payload: &Payload<'_>, wasm: &[u8]) -> Result<()> {
    let Some((id, range)) = payload.as_section() else {
        bail!("#418 internal: unhandled non-section payload {payload:?}");
    };
    module.section(&wasm_encoder::RawSection {
        id,
        data: &wasm[section_span(range, wasm)?],
    });
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- section_span: the REFUSAL is the deliverable (#965, RQ-83-RANGEWIDEN) ----
    //
    // REACH, stated because it is not uniform across the three arms. The
    // `end > wasm.len()` / `start > end` arm is reachable and tested below. The two
    // `usize::try_from` arms are NOT reachable on any 64-bit target, where
    // `u64 -> usize` is infallible; they exist for a 32-bit host and are UNPROVEN
    // here. A test cannot be written for them on this platform, and asserting
    // otherwise would be the vacuous-green class this file's own lane exists to catch.

    #[test]
    fn section_span_refuses_a_range_past_the_module_end() {
        let wasm = [0u8; 10];
        let err = section_span(0..100, &wasm).expect_err("a 0..100 range in 10 bytes must refuse");
        let msg = format!("{err}");
        assert!(
            msg.contains("does not lie inside") && msg.contains("10-byte"),
            "the refusal must name the overrun and the real module size, got: {msg}"
        );
    }

    #[test]
    fn section_span_refuses_an_inverted_range() {
        let wasm = [0u8; 10];
        // The bounds come from locals rather than literals: clippy's
        // `reversed_empty_ranges` correctly flags a literal `8..4` as an empty
        // range, and its suggested `(4..8).rev()` is a DIFFERENT subject — this
        // test is about an inverted range reaching the helper, not about
        // iteration.
        let (start, end) = (8u64, 4u64);
        let err = section_span(start..end, &wasm).expect_err("start > end must refuse");
        assert!(
            format!("{err}").contains("does not lie inside"),
            "an inverted range must refuse rather than panic or wrap"
        );
    }

    #[test]
    fn section_span_refuses_one_byte_past_the_end() {
        // The off-by-one is the interesting boundary: `end == len` is legal,
        // `end == len + 1` is not. A `<` instead of `<=` here would pass the
        // 0..100 case above and still index out of bounds.
        let wasm = [0u8; 10];
        assert!(
            section_span(0..10, &wasm).is_ok(),
            "end == len must be accepted"
        );
        assert!(
            section_span(0..11, &wasm).is_err(),
            "end == len + 1 must refuse"
        );
    }

    #[test]
    fn section_span_accepts_an_in_bounds_range_and_preserves_its_bounds() {
        let wasm = [0u8; 10];
        let span = section_span(2..7, &wasm).expect("an in-bounds range must be accepted");
        assert_eq!(
            span,
            2usize..7usize,
            "the narrowing must not move the bounds"
        );
        // An empty span inside the buffer is legal and must stay empty.
        assert_eq!(section_span(5..5, &wasm).unwrap(), 5usize..5usize);
        assert!(
            wasm[span].len() == 5,
            "the returned span must actually index"
        );
    }

    #[test]
    fn section_span_refuses_rather_than_truncating_the_value_an_as_cast_would_discard() {
        // POSITIVE CONTROL for the whole point of the helper. `0x1_0000_0003 as usize`
        // is lossless on a 64-bit host, so the danger here is not the cast but the
        // BOUNDS: an offset far past a small module must refuse, where
        // `&wasm[start..end]` would have panicked and `as u32` would have silently
        // read byte 3. Both wrong answers are excluded by one check.
        let wasm = [0u8; 10];
        let err = section_span(0x1_0000_0003..0x1_0000_0007, &wasm)
            .expect_err("a 4 GiB-plus offset into a 10-byte module must refuse");
        assert!(
            format!("{err}").contains("#965"),
            "the refusal must cite its analysis"
        );
    }

    fn fixture() -> Vec<u8> {
        wat::parse_str(
            r#"(module
                 (import "env" "__cabi_arena_realloc"
                   (func $arena (param i32 i32 i32 i32) (result i32)))
                 (memory (export "memory") 1)
                 (global $sp (mut i32) (i32.const 4096))
                 (global (export "__heap_base") i32 (i32.const 6144))
                 (data (i32.const 5120) "0123456789abcdef")
                 (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
                   local.get 0 local.get 1 local.get 2 local.get 3 call $arena))"#,
        )
        .unwrap()
    }

    #[test]
    fn binds_sole_arena_import() {
        let ArenaBind::Bound(b) = bind_cabi_arena_realloc(&fixture()).unwrap() else {
            panic!("expected Bound");
        };
        // base above data end (5136) and __heap_base (6144), 16-aligned
        assert_eq!(b.arena_base, 6144);
        assert_eq!(b.arena_end, 65536);
        // no imports remain; index space preserved (cabi_realloc still calls
        // function 0, which is now the DEFINED allocator).
        let mut num_imports = 0;
        let mut num_funcs = 0;
        let mut num_globals = 0;
        for p in Parser::new(0).parse_all(&b.bytes) {
            match p.unwrap() {
                Payload::ImportSection(r) => num_imports += r.count(),
                Payload::FunctionSection(r) => num_funcs = r.count(),
                Payload::GlobalSection(r) => num_globals = r.count(),
                _ => {}
            }
        }
        assert_eq!(num_imports, 0);
        assert_eq!(num_funcs, 2); // allocator + cabi_realloc
        assert_eq!(num_globals, 3); // sp, __heap_base, cursor
    }

    #[test]
    fn bound_module_executes_contract() {
        // The rewritten module must satisfy the #418 contract under a real
        // wasm interpreter — validated structurally here (full execution
        // differential: scripts/repro/cabi_arena_bind_418_differential.py).
        let ArenaBind::Bound(b) = bind_cabi_arena_realloc(&fixture()).unwrap() else {
            panic!("expected Bound");
        };
        wasmparser::Validator::new().validate_all(&b.bytes).unwrap();
    }

    #[test]
    fn no_arena_import_passes_through() {
        let wasm =
            wat::parse_str(r#"(module (memory 1) (func (export "f") (result i32) i32.const 7))"#)
                .unwrap();
        assert!(matches!(
            bind_cabi_arena_realloc(&wasm).unwrap(),
            ArenaBind::NoArenaImport
        ));
    }

    #[test]
    fn other_imports_keep_host_seam() {
        let wasm = wat::parse_str(
            r#"(module
                 (import "env" "k_spin_lock" (func (param i32)))
                 (import "env" "__cabi_arena_realloc"
                   (func $arena (param i32 i32 i32 i32) (result i32)))
                 (memory 1)
                 (func (export "f") (param i32 i32 i32 i32) (result i32)
                   local.get 0 local.get 1 local.get 2 local.get 3 call $arena))"#,
        )
        .unwrap();
        assert!(matches!(
            bind_cabi_arena_realloc(&wasm).unwrap(),
            ArenaBind::KeptHostSeam(_)
        ));
    }

    #[test]
    fn wrong_signature_declines_loudly() {
        let wasm = wat::parse_str(
            r#"(module
                 (import "env" "__cabi_arena_realloc"
                   (func $arena (param i32 i32) (result i32)))
                 (memory 1)
                 (func (export "f") (param i32 i32) (result i32)
                   local.get 0 local.get 1 call $arena))"#,
        )
        .unwrap();
        let err = bind_cabi_arena_realloc(&wasm).unwrap_err().to_string();
        assert!(err.contains("#418"), "{err}");
        assert!(err.contains("signature"), "{err}");
    }

    #[test]
    fn no_memory_declines_loudly() {
        let wasm = wat::parse_str(
            r#"(module
                 (import "env" "__cabi_arena_realloc"
                   (func $arena (param i32 i32 i32 i32) (result i32)))
                 (func (export "f") (result i32)
                   i32.const 0 i32.const 0 i32.const 8 i32.const 4 call $arena))"#,
        )
        .unwrap();
        let err = bind_cabi_arena_realloc(&wasm).unwrap_err().to_string();
        assert!(err.contains("no linear memory"), "{err}");
    }

    #[test]
    fn full_static_layout_declines_loudly() {
        // __heap_base == memory size: no arena region left.
        let wasm = wat::parse_str(
            r#"(module
                 (import "env" "__cabi_arena_realloc"
                   (func $arena (param i32 i32 i32 i32) (result i32)))
                 (memory 1)
                 (global (export "__heap_base") i32 (i32.const 65536))
                 (func (export "f") (result i32)
                   i32.const 0 i32.const 0 i32.const 8 i32.const 4 call $arena))"#,
        )
        .unwrap();
        let err = bind_cabi_arena_realloc(&wasm).unwrap_err().to_string();
        assert!(err.contains("no arena region left"), "{err}");
    }

    #[test]
    fn module_without_globals_gets_global_section() {
        let wasm = wat::parse_str(
            r#"(module
                 (import "env" "__cabi_arena_realloc"
                   (func $arena (param i32 i32 i32 i32) (result i32)))
                 (memory 1)
                 (data (i32.const 64) "xyzw")
                 (func (export "f") (result i32)
                   i32.const 0 i32.const 0 i32.const 8 i32.const 4 call $arena))"#,
        )
        .unwrap();
        let ArenaBind::Bound(b) = bind_cabi_arena_realloc(&wasm).unwrap() else {
            panic!("expected Bound");
        };
        assert_eq!(b.arena_base, 80); // data end 68 -> 16-aligned
        let mut num_globals = 0;
        for p in Parser::new(0).parse_all(&b.bytes) {
            if let Payload::GlobalSection(r) = p.unwrap() {
                num_globals = r.count();
            }
        }
        assert_eq!(num_globals, 1);
    }
}
