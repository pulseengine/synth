//! VCR-MEM-001 layer-2 (#678) — down-shift inline linmem statics into the
//! shrunk native-pointer reservation.
//!
//! Layer-1 (#383) refused any `__synth_wasm_data + C` reloc with `C != 0` still
//! pointing into the `[0, sp_init)` reservation ("down-shifting inline statics is
//! the deferred general case"). That refusal gated every buffer-carrying dissolved
//! node (wit-bindgen `list<u8>`) and every plain `static mut` array on a tiny MCU.
//! Layer-2 rebases those tail statics `C -> C - (sp_init - budget)` so the node
//! links; the execution differential lives in
//! `scripts/repro/native_pointer_static_downshift_678.py` (a shadow-stack
//! roundtrip plus a `.data` buffer plus a down-shifted BSS static, all agreeing
//! with wasmtime).

use std::path::PathBuf;
use std::process::Command;

// #977 RQ-59-FRESHNESS: nothing here parses an artifact until the artifact is
// proven to be THIS invocation's output — see `artifact_guard`. The readers
// below take BYTES, not a path, so no read can outlive its compile.
mod artifact_guard;

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn repro(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

fn compile(fixture: &str, extra: &[&str], out: &str) -> std::process::Output {
    let fx = repro(fixture);
    let mut args = vec![
        "compile",
        fx.to_str().unwrap(),
        "--target",
        "cortex-m3",
        "--native-pointer-abi",
        "--all-exports",
        "--relocatable",
        "-o",
        out,
    ];
    args.extend_from_slice(extra);
    Command::new(synth())
        .args(&args)
        .output()
        .expect("run synth")
}

/// #977: the guarded READ-BACK form — compile and hand back the object bytes
/// proven to be this invocation's output. [`compile`] above stays for the
/// straddle refusal test, which never reads an artifact.
fn compile_read(fixture: &str, extra: &[&str], tag: &str) -> Vec<u8> {
    let fx = repro(fixture);
    let out = artifact_guard::unique_artifact(tag, "o");
    let mut args = vec![
        "compile",
        fx.to_str().unwrap(),
        "--target",
        "cortex-m3",
        "--native-pointer-abi",
        "--all-exports",
        "--relocatable",
        "-o",
        out.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    let mut cmd = Command::new(synth());
    cmd.args(&args);
    artifact_guard::compile_bytes_or_panic(&mut cmd, &out, tag)
}

fn bss_size(data: &[u8]) -> u64 {
    let obj = object::File::parse(data).expect("parse ELF");
    obj.sections()
        .find(|s| s.name() == Ok(".bss"))
        .expect(".bss present")
        .size()
}

/// The in-place REL addend of the (unique) `__synth_wasm_data` R_ARM_ABS32 reloc
/// whose in-place literal word is non-zero — i.e. the down-shifted static addend.
fn max_wasm_data_addend(bytes: &[u8]) -> u32 {
    let obj = object::File::parse(bytes).expect("parse ELF");
    let text = obj.section_by_name(".text").expect(".text");
    let text_data = text.data().expect("text data");
    let mut best = 0u32;
    for (off, reloc) in text.relocations() {
        if let RelocationTarget::Symbol(sidx) = reloc.target() {
            let sym = obj.symbol_by_index(sidx).expect("sym");
            if sym.name() == Ok("__synth_wasm_data") {
                let p = off as usize;
                let word = u32::from_le_bytes(text_data[p..p + 4].try_into().unwrap());
                best = best.max(word);
            }
        }
    }
    best
}

/// RED before the fix / GREEN after: a plain BSS static (`split_linmem_bss`
/// geometry, no `(data)` segment) at wasm addr 4160 down-shifts by
/// `sp_init(4096) - budget(512) = 3584` to object offset 576, and the reservation
/// shrinks to `budget + tail`.
#[test]
fn bss_static_downshifts_678() {
    let bytes = compile_read(
        "mem678_bss.wat",
        &["--shadow-stack-size", "512"],
        "mem678_bss_test",
    );
    assert_eq!(
        max_wasm_data_addend(&bytes),
        576,
        "static at 4160 must rebase to 4160 - (4096-512) = 576"
    );
    // budget 512 + static tail (used_extent 4168 - sp_init 4096 = 72) = 584.
    assert_eq!(bss_size(&bytes), 584);
}

/// Mixed geometry: a `(data)` segment (retargeted to `.data`) AND a BSS static at
/// 4200 (down-shifted). Both mechanisms coexist — the segment read stays in
/// `.data`, only the residual BSS reloc is rebased (4200 - 3584 = 616).
#[test]
fn buffer_plus_bss_downshifts_678() {
    let bytes = compile_read(
        "mem678_buf.wat",
        &["--shadow-stack-size", "512"],
        "mem678_buf_test",
    );
    assert_eq!(
        max_wasm_data_addend(&bytes),
        616,
        "bss static at 4200 must rebase to 616; the data-seg read stays in .data"
    );
}

/// Sound-decline: a load window that straddles a `(data)` segment boundary from
/// just below has part of its bytes in `.data` and part in the `.bss` tail — it
/// cannot be down-shifted soundly, so it is refused LOUDLY with a precise reason
/// (not a blanket refusal).
#[test]
fn straddling_static_refused_678() {
    let out = compile(
        "mem678_straddle.wat",
        &["--shadow-stack-size", "512"],
        "/tmp/mem678_straddle_test.o",
    );
    assert!(!out.status.success(), "straddle must be refused");
    let log = String::from_utf8_lossy(&out.stderr);
    assert!(
        log.contains("straddles an initialized (data) segment"),
        "expected the precise straddle decline; got:\n{log}"
    );
}

/// Opt-in / frozen-safe: WITHOUT the flag the same buffer node keeps the full
/// reservation and no static is rebased (byte-identical to pre-#678).
#[test]
fn no_flag_leaves_statics_inline_678() {
    let bytes = compile_read("mem678_buf.wat", &[], "mem678_buf_noflag");
    // Un-shifted: the bss static keeps its full wasm addend 4200.
    assert_eq!(max_wasm_data_addend(&bytes), 4200);
}
