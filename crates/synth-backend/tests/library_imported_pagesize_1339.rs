//! RQ-89-IMPSIZE (the imported-memory residual of #1339): an IMPORTED
//! `(pagesize 1)` memory 0 through the published `Backend` API is honoured
//! and refused exactly where a DEFINED one is (RQ-89-PAGESIZEAPI).
//!
//! `ArmBackend::compile_module` checked and read the DEFINED-memory list only,
//! so an imported `(pagesize 1)` was never refused off `relocatable`, and on
//! `relocatable` `memory.size` kept the default config's 16-bit shift
//! (`R10 >> 16` = 0 for a 20000-byte memory; wasmtime says 20000).

use synth_backend::ArmBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::wasm_decoder::decode_wasm_module;

/// `(module (import "env" "m0" (memory 20000 20000 (pagesize 1)))
///   (func (export "ms") (result i32) (memory.size)))`
const IMPORTED_PAGESIZE_1: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, 0x02,
    0x11, 0x01, 0x03, 0x65, 0x6e, 0x76, 0x02, 0x6d, 0x30, 0x02, 0x09, 0xa0, 0x9c, 0x01, 0xa0, 0x9c,
    0x01, 0x00, 0x03, 0x02, 0x01, 0x00, 0x07, 0x06, 0x01, 0x02, 0x6d, 0x73, 0x00, 0x00, 0x0a, 0x06,
    0x01, 0x04, 0x00, 0x3f, 0x00, 0x0b,
];

fn module_code(config: &CompileConfig) -> Result<Vec<u8>, String> {
    let module = decode_wasm_module(IMPORTED_PAGESIZE_1).expect("decodes");
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

#[test]
fn decoder_reports_the_imported_declaration_1339() {
    let m = decode_wasm_module(IMPORTED_PAGESIZE_1).expect("decodes");
    assert!(m.memories.is_empty(), "the memory is imported, not defined");
    let mem0 = m.memory0().expect("memory 0 is the import");
    assert_eq!(mem0.page_size_log2, Some(0));
    assert_eq!(mem0.initial_bytes(), 20000);
}

/// RED on base: `LSR.W r0, r10, #16` (memory.size = 0 for 20000 bytes).
#[test]
fn relocatable_honours_imported_pagesize_1_1339() {
    let code = module_code(&CompileConfig {
        relocatable: true,
        ..CompileConfig::default()
    })
    .expect("(pagesize 1) is HONOURED on the relocatable path");
    let mov_r0_r10: &[u8] = &[0x4f, 0xea, 0x0a, 0x00];
    let lsr16: &[u8] = &[0x4f, 0xea, 0x1a, 0x40];
    assert!(code.windows(4).any(|w| w == mov_r0_r10), "{code:02x?}");
    assert!(!code.windows(4).any(|w| w == lsr16), "{code:02x?}");
}

/// RED on base: rc-Ok with `LSR #16` on the optimized path.
#[test]
fn non_relocatable_refuses_imported_pagesize_1_1339() {
    let err = module_code(&CompileConfig::default())
        .expect_err("the optimized path cannot lower (pagesize 1)");
    assert!(err.contains("(pagesize 1)"), "names the page size: {err}");
}
