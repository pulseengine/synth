//! synth#418 — embedder import `cabi-arena-realloc` binds to the native TCB
//! arena allocator via synth's relocatable host-link path (#197).
//!
//! In the BYO-OS lean-MCU dissolve (gale#89), grow-free components route
//! `cabi_realloc` to an embedder-provided `env::__cabi_arena_realloc` import
//! (wit-bindgen `cabi-realloc-extern`). synth operates on the CORE module, so it
//! sees the verbatim core field name `__cabi_arena_realloc` (the kebab
//! `cabi-arena-realloc` is a component-surface concern, never reaching synth),
//! and its `--relocatable` import-call path (#197) lowers the call to a direct
//! `R_ARM_THM_CALL` relocation against an UNDEFINED `__cabi_arena_realloc`
//! symbol — which the native link binds to the TCB's arena allocator. synth
//! references the symbol; the TCB provides it; the linker binds it (the correct
//! layering — synth never implements the allocator or the realloc contract).
//!
//! This locks that mechanism. The full end-to-end check on gale's real dissolved
//! component (out of the wit-bindgen#4 → wasm-tools#2 → meld#301 pipeline) lands
//! when that fixture arrives; this proves the synth-layer contract synthetically.

use std::path::PathBuf;
use std::process::Command;

use object::read::elf::ElfFile32;
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

// #977 RQ-59-FRESHNESS: nothing here parses an artifact until the artifact is
// proven to be THIS invocation's output — see `artifact_guard`.
mod artifact_guard;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/cabi_arena_realloc.wat")
}

#[test]
fn cabi_arena_realloc_emits_undefined_symbol_and_reloc_418() {
    // #977: unique per call + remove-first + status/exists/non-empty guards.
    let out = artifact_guard::unique_artifact("cabi_arena_realloc_418", "o");
    let mut cmd = Command::new(synth());
    cmd.args([
        "compile",
        fixture().to_str().unwrap(),
        "--target",
        "cortex-m4",
        "--native-pointer-abi",
        "--all-exports",
        "--relocatable",
        "-o",
        out.to_str().unwrap(),
    ]);
    let data = artifact_guard::compile_bytes_or_panic(&mut cmd, &out, "cabi_arena_realloc.wat");
    let obj = ElfFile32::<object::Endianness>::parse(&*data).expect("parse ELF");

    // (1) `__cabi_arena_realloc` is present as an UNDEFINED symbol — left for the
    // native link / TCB to satisfy, not implemented by synth.
    let sym = obj
        .symbols()
        .find(|s| s.name() == Ok("__cabi_arena_realloc"))
        .expect("__cabi_arena_realloc symbol present");
    assert!(
        sym.is_undefined(),
        "__cabi_arena_realloc must be UNDEFINED (embedder-bound), not defined in synth's output"
    );

    // (2) a relocation targets that symbol at the call site — so the native
    // linker rewrites the `bl` to the TCB's arena allocator.
    let mut reloc_targets_arena = false;
    for section in obj.sections() {
        for (_off, reloc) in section.relocations() {
            if let RelocationTarget::Symbol(idx) = reloc.target()
                && let Ok(s) = obj.symbol_by_index(idx)
                && s.name() == Ok("__cabi_arena_realloc")
            {
                reloc_targets_arena = true;
            }
        }
    }
    assert!(
        reloc_targets_arena,
        "a relocation must target __cabi_arena_realloc (the import call site), \
         so the native link binds it to the TCB allocator"
    );
}
