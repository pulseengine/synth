//! synth#418 — SELF-CONTAINED binding of `env::__cabi_arena_realloc`.
//!
//! Companion to `cabi_arena_realloc_linkability_418.rs` (which locks the
//! `--relocatable` seam: an UNDEFINED symbol the TCB satisfies at native
//! link). This file locks the OTHER half of #418: on the default
//! self-contained Cortex-M path a sole arena import is bound to a synthesized
//! in-module allocator, producing an ET_EXEC image with no external seam —
//! plus the decline matrix around that binding. Execution correctness is
//! gated by `scripts/repro/cabi_arena_bind_418_differential.py` (CI job
//! `arena-bind-418-oracle`).

use std::path::PathBuf;
use std::process::Command;

use object::read::elf::ElfFile32;
use object::{Object, ObjectSymbol};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/cabi_arena_bind.wat")
}

/// ELF e_type from the raw header (1 = ET_REL, 2 = ET_EXEC).
fn e_type(data: &[u8]) -> u16 {
    u16::from_le_bytes([data[16], data[17]])
}

fn compile(args: &[&str], out: &str) -> std::process::Output {
    let mut cmd = Command::new(synth());
    cmd.args(["compile", fixture().to_str().unwrap()])
        .args(args)
        .args(["--target", "cortex-m3", "--all-exports", "-o", out])
        // The binding log line is part of the asserted surface below;
        // INFO-level tracing is off by default in a non-TTY test run.
        .env("RUST_LOG", "info");
    cmd.output().expect("run synth")
}

fn has_undefined_arena(data: &[u8]) -> bool {
    let obj = ElfFile32::<object::Endianness>::parse(data).expect("parse ELF");
    obj.symbols()
        .any(|s| s.name() == Ok("__cabi_arena_realloc") && s.is_undefined())
}

/// Default self-contained compile: the arena import is BOUND — the output is
/// an executable image with no `__cabi_arena_realloc` seam left.
#[test]
fn self_contained_binds_arena_import_418() {
    let out = "/tmp/cabi_arena_bind_418_default.elf";
    let r = compile(&[], out);
    assert!(
        r.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&r.stderr)
    );
    // tracing INFO may land on either stream depending on subscriber config.
    let logs = format!(
        "{}{}",
        String::from_utf8_lossy(&r.stdout),
        String::from_utf8_lossy(&r.stderr)
    );
    assert!(
        logs.contains("#418: bound env::__cabi_arena_realloc"),
        "expected the #418 binding log line, got: {logs}"
    );
    let data = std::fs::read(out).unwrap();
    assert_eq!(
        e_type(&data),
        2,
        "bound module must be a self-contained ET_EXEC image, not a link-me object"
    );
    assert!(
        !has_undefined_arena(&data),
        "no undefined __cabi_arena_realloc may remain in the bound image"
    );
}

/// The pinned opt-out restores the pass-through: ET_REL with the undefined
/// external symbol (the embedder seam), byte-compatible with the old behavior.
#[test]
fn opt_out_restores_external_seam_418() {
    let out = "/tmp/cabi_arena_bind_418_optout.elf";
    let r = compile(&["--no-bind-cabi-arena"], out);
    assert!(
        r.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&r.stderr)
    );
    let data = std::fs::read(out).unwrap();
    assert_eq!(
        e_type(&data),
        1,
        "opt-out must produce ET_REL (host-linked)"
    );
    assert!(
        has_undefined_arena(&data),
        "opt-out must keep __cabi_arena_realloc an UNDEFINED external symbol"
    );
}

/// `--relocatable` keeps the #420 layering untouched: synth references, the
/// TCB provides, the linker binds — no in-image allocator.
#[test]
fn relocatable_keeps_tcb_seam_418() {
    let out = "/tmp/cabi_arena_bind_418_reloc.elf";
    let r = compile(&["--relocatable"], out);
    assert!(
        r.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&r.stderr)
    );
    let data = std::fs::read(out).unwrap();
    assert_eq!(e_type(&data), 1);
    assert!(
        has_undefined_arena(&data),
        "--relocatable must keep the undefined TCB-bound symbol (#420 contract)"
    );
}

/// A wrong-signature arena import is NOT the documented contract: the compile
/// refuses loudly instead of guessing an ABI (honest degradation).
#[test]
fn wrong_signature_declines_loudly_418() {
    let wat = r#"(module
      (import "env" "__cabi_arena_realloc" (func $a (param i32 i32) (result i32)))
      (memory 1)
      (func (export "f") (param i32 i32) (result i32)
        local.get 0 local.get 1 call $a))"#;
    let path = std::env::temp_dir().join("cabi_arena_bind_418_bad_sig.wat");
    std::fs::write(&path, wat).unwrap();
    let out = "/tmp/cabi_arena_bind_418_bad_sig.elf";
    let r = Command::new(synth())
        .args(["compile", path.to_str().unwrap()])
        .args(["--target", "cortex-m3", "--all-exports", "-o", out])
        .output()
        .expect("run synth");
    assert!(!r.status.success(), "wrong-signature bind must fail loudly");
    let stderr = String::from_utf8_lossy(&r.stderr);
    assert!(
        stderr.contains("#418") && stderr.contains("signature"),
        "expected the precise #418 signature decline, got: {stderr}"
    );
}

/// With OTHER imports alongside the arena import the module cannot
/// self-contain — the arena import stays on the host-linked seam (pass-through
/// to ET_REL, undefined symbol), never a half-bound hybrid.
#[test]
fn other_imports_keep_host_seam_418() {
    let wat = r#"(module
      (import "env" "k_spin_lock" (func (param i32)))
      (import "env" "__cabi_arena_realloc"
        (func $a (param i32 i32 i32 i32) (result i32)))
      (memory 1)
      (func (export "f") (param i32 i32 i32 i32) (result i32)
        local.get 0 local.get 1 local.get 2 local.get 3 call $a))"#;
    let path = std::env::temp_dir().join("cabi_arena_bind_418_mixed.wat");
    std::fs::write(&path, wat).unwrap();
    let out = "/tmp/cabi_arena_bind_418_mixed.elf";
    let r = Command::new(synth())
        .args(["compile", path.to_str().unwrap()])
        .args(["--target", "cortex-m3", "--all-exports", "-o", out])
        .output()
        .expect("run synth");
    assert!(
        r.status.success(),
        "mixed-import module must still compile (host-linked): {}",
        String::from_utf8_lossy(&r.stderr)
    );
    let data = std::fs::read(out).unwrap();
    assert_eq!(e_type(&data), 1, "mixed imports keep the ET_REL host seam");
    assert!(
        has_undefined_arena(&data),
        "the arena import must stay an undefined external alongside other imports"
    );
}
