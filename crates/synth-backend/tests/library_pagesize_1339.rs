//! RQ-89-PAGESIZEAPI (#1339): a custom page size reaching the PUBLISHED
//! `Backend` API — not the CLI — is honoured where the lowering reads the
//! declared page size, and refused LOUDLY everywhere else.
//!
//! Before this, `refuse_custom_page_size` lived only in `synth-cli`. A library
//! caller that decoded a `(pagesize 1)` module and handed it to
//! `ArmBackend::compile_module` got rc-Ok on EVERY path, with `memory.size`
//! lowered as `R10 >> 16` because `CompileConfig::default()` carries
//! `memory0_page_log2: 16` and nothing derived it from the module. For the
//! 20000-byte memory below, wasmtime answers `memory.size` = 20000; the
//! library-compiled code answered 20000 >> 16 = 0.
//!
//! What the CLI does per path, and what the library now does on the same path:
//!   * `--relocatable` (direct selector, #197): HONOURED — `memory.size` is
//!     `MOV rd, R10` (#1441). The library DERIVES the shift from the module
//!     instead of trusting the caller's config, which is the honour gale asked
//!     for on #1145 (RQ-71-PAGELIB); nothing here moves a refusal into the
//!     `synth-core` decoder (RQ-81-PAGESIZE3 built that and reverted it).
//!   * not relocatable (optimized path, hardcoded `LSR #16`): REFUSED, naming
//!     the page size.

use synth_backend::ArmBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::wasm_decoder::decode_wasm_module;

/// `(module (memory 20000 20000 (pagesize 1))
///   (func (export "ms") (result i32) (memory.size)))`
const PAGESIZE_1: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, 0x03,
    0x02, 0x01, 0x00, 0x05, 0x09, 0x01, 0x09, 0xa0, 0x9c, 0x01, 0xa0, 0x9c, 0x01, 0x00, 0x07, 0x06,
    0x01, 0x02, 0x6d, 0x73, 0x00, 0x00, 0x0a, 0x06, 0x01, 0x04, 0x00, 0x3f, 0x00, 0x0b,
];

/// `(module (memory 1 1) (func (export "ms") (result i32) (memory.size)))`
const DEFAULT_PAGE: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, 0x03,
    0x02, 0x01, 0x00, 0x05, 0x04, 0x01, 0x01, 0x01, 0x01, 0x07, 0x06, 0x01, 0x02, 0x6d, 0x73, 0x00,
    0x00, 0x0a, 0x06, 0x01, 0x04, 0x00, 0x3f, 0x00, 0x0b,
];

fn relocatable() -> CompileConfig {
    CompileConfig {
        relocatable: true,
        ..CompileConfig::default()
    }
}

fn module_code(wasm: &[u8], config: &CompileConfig) -> Result<Vec<u8>, String> {
    let module = decode_wasm_module(wasm).expect("decodes");
    ArmBackend::new()
        .compile_module(&module, config)
        .map(|r| {
            r.functions
                .into_iter()
                .find(|f| f.name == "ms")
                .expect("ms compiled")
                .code
        })
        .map_err(|e| e.to_string())
}

fn function_code(wasm: &[u8], config: &CompileConfig) -> Result<Vec<u8>, String> {
    let module = decode_wasm_module(wasm).expect("decodes");
    let f = module
        .functions
        .iter()
        .find(|f| f.export_name.as_deref() == Some("ms"))
        .expect("ms present");
    ArmBackend::new()
        .compile_function("ms", &f.ops, config)
        .map(|c| c.code)
        .map_err(|e| e.to_string())
}

/// The decoder reads the declaration (this half was never the defect).
#[test]
fn decoder_reports_the_declared_byte_extent_1339() {
    let m = decode_wasm_module(PAGESIZE_1).expect("decodes");
    assert_eq!(m.memories[0].page_size_log2, Some(0));
    assert_eq!(m.memories[0].initial_bytes(), 20000);
}

/// RED on base: `compile_module` ignored the declaration and lowered
/// `memory.size` with the default config's 16-bit shift.
#[test]
fn relocatable_compile_module_honours_pagesize_1_1339() {
    let honoured = function_code(
        PAGESIZE_1,
        &CompileConfig {
            memory0_page_log2: 0,
            ..relocatable()
        },
    )
    .expect("the explicit-config compile is the #1441 capability");
    let shifted = function_code(PAGESIZE_1, &relocatable()).expect("default-config compile");
    assert_ne!(
        honoured, shifted,
        "the two shifts must differ, or this test is vacuous"
    );
    let via_module = module_code(PAGESIZE_1, &relocatable())
        .expect("(pagesize 1) is HONOURED on the relocatable path");
    assert_eq!(
        via_module, honoured,
        "compile_module must derive memory 0's page size from the MODULE: \
         with the default config it emitted `R10 >> 16` (memory.size = 0 for a \
         20000-byte memory; wasmtime says 20000)"
    );
    // The exact instruction #1441 measured and the lane's unicorn run executed
    // (R10 = 20000 -> R0 = 20000, matching wasmtime): `MOV.W r0, r10`, where
    // the default page emits `LSR.W r0, r10, #16` (`4f ea 1a 40`).
    let mov_r0_r10: &[u8] = &[0x4f, 0xea, 0x0a, 0x00];
    let lsr16: &[u8] = &[0x4f, 0xea, 0x1a, 0x40];
    assert!(
        via_module.windows(4).any(|w| w == mov_r0_r10),
        "{via_module:02x?}"
    );
    assert!(
        !via_module.windows(4).any(|w| w == lsr16),
        "{via_module:02x?}"
    );
}

/// RED on base: rc-Ok with `LSR #16` on the optimized path.
#[test]
fn non_relocatable_compile_module_refuses_pagesize_1_1339() {
    let err = module_code(PAGESIZE_1, &CompileConfig::default())
        .expect_err("(pagesize 1) off --relocatable must be refused");
    assert!(err.contains("(pagesize 1)"), "names the page size: {err}");
    assert!(err.contains("#1339"), "cites the analysis: {err}");
}

/// RED on base: `compile_function` carries no module, but its config can still
/// say memory 0 is byte-paged — and the optimized path's `memory.size` would
/// ignore that and shift by a literal 16.
#[test]
fn non_relocatable_compile_function_refuses_byte_paged_config_1339() {
    let err = function_code(
        PAGESIZE_1,
        &CompileConfig {
            memory0_page_log2: 0,
            ..CompileConfig::default()
        },
    )
    .expect_err("a byte-paged config off --relocatable must be refused");
    assert!(err.contains("(pagesize 1)"), "names the page size: {err}");
}

/// Positive control: the default page compiles on both paths, and
/// `compile_module` agrees with the CLI-shaped explicit config.
#[test]
fn default_page_size_still_compiles_on_both_paths_1339() {
    for cfg in [CompileConfig::default(), relocatable()] {
        let m = module_code(DEFAULT_PAGE, &cfg).expect("default page compiles");
        let f = function_code(DEFAULT_PAGE, &cfg).expect("default page compiles");
        assert_eq!(m, f);
    }
}
