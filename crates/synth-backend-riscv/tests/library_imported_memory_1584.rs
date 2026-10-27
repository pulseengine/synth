//! RQ-89-IMPSIZE (#1584, and the imported-memory residual of #1339): an
//! IMPORTED memory 0 through the published `Backend` API on RV32.
//!
//! `compile_module` read memory 0 from the DEFINED-memory list only, so an
//! imported-only module was sized as zero bytes, and its per-memory page-size
//! check never saw an imported `(pagesize 1)`. This backend bakes memory 0's
//! size into the code, so an import is sized from its declaration only when
//! its limits PIN the size (maximum == minimum); any other import is refused,
//! as is an imported `(pagesize 1)` (refused for a defined memory too).

use synth_backend_riscv::RiscVBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::target::TargetSpec;
use synth_core::wasm_decoder::decode_wasm_module;

/// `(module (import "env" "m0" (memory 1 2)) (func (export "ms") (result i32) (memory.size)))`
const IMPORTED_1_2: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, 0x02,
    0x0c, 0x01, 0x03, 0x65, 0x6e, 0x76, 0x02, 0x6d, 0x30, 0x02, 0x01, 0x01, 0x02, 0x03, 0x02, 0x01,
    0x00, 0x07, 0x06, 0x01, 0x02, 0x6d, 0x73, 0x00, 0x00, 0x0a, 0x06, 0x01, 0x04, 0x00, 0x3f, 0x00,
    0x0b,
];

/// `(module (import "env" "m0" (memory 2 2)) (func (export "ms") (result i32) (memory.size)))`
const IMPORTED_2_2: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, 0x02,
    0x0c, 0x01, 0x03, 0x65, 0x6e, 0x76, 0x02, 0x6d, 0x30, 0x02, 0x01, 0x02, 0x02, 0x03, 0x02, 0x01,
    0x00, 0x07, 0x06, 0x01, 0x02, 0x6d, 0x73, 0x00, 0x00, 0x0a, 0x06, 0x01, 0x04, 0x00, 0x3f, 0x00,
    0x0b,
];

/// `(module (memory 2 2) (func (export "ms") (result i32) (memory.size)))`
const DEFINED_2_2: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, 0x03,
    0x02, 0x01, 0x00, 0x05, 0x04, 0x01, 0x01, 0x02, 0x02, 0x07, 0x06, 0x01, 0x02, 0x6d, 0x73, 0x00,
    0x00, 0x0a, 0x06, 0x01, 0x04, 0x00, 0x3f, 0x00, 0x0b,
];

/// `(module (import "env" "m0" (memory 20000 20000 (pagesize 1)))
///   (func (export "ms") (result i32) (memory.size)))`
const IMPORTED_PAGESIZE_1: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, 0x02,
    0x11, 0x01, 0x03, 0x65, 0x6e, 0x76, 0x02, 0x6d, 0x30, 0x02, 0x09, 0xa0, 0x9c, 0x01, 0xa0, 0x9c,
    0x01, 0x00, 0x03, 0x02, 0x01, 0x00, 0x07, 0x06, 0x01, 0x02, 0x6d, 0x73, 0x00, 0x00, 0x0a, 0x06,
    0x01, 0x04, 0x00, 0x3f, 0x00, 0x0b,
];

fn cfg() -> CompileConfig {
    CompileConfig {
        target: TargetSpec::riscv32imac(),
        relocatable: true,
        ..CompileConfig::default()
    }
}

fn module_code(wasm: &[u8]) -> Result<Vec<u8>, String> {
    let module = decode_wasm_module(wasm).expect("decodes");
    RiscVBackend
        .compile_module(&module, &cfg())
        .map(|r| {
            r.functions
                .into_iter()
                .find(|f| f.name == "ms")
                .expect("ms compiled")
                .code
        })
        .map_err(|e| e.to_string())
}

/// RED on base: the import was invisible, so this compiled with memory 0
/// sized from nothing.
#[test]
fn unpinned_imported_memory_is_refused_1584() {
    let err = module_code(IMPORTED_1_2).expect_err("min 1 / max 2 does not pin the size");
    assert!(err.contains("#1584"), "cites the analysis: {err}");
    assert!(err.contains("imported"), "names the import: {err}");
}

/// RED on base: `memory.size` lowered against a ZERO-byte memory 0. A pinned
/// import must lower exactly like a defined memory with the same limits.
#[test]
fn pinned_imported_memory_lowers_like_the_defined_one_1584() {
    let imported = module_code(IMPORTED_2_2).expect("min == max pins the size");
    let defined = module_code(DEFINED_2_2).expect("defined (memory 2 2)");
    assert_eq!(
        imported, defined,
        "imported (memory 2 2) must size memory 0 as 2 pages"
    );
}

/// RED on base: an imported `(pagesize 1)` compiled Ok.
#[test]
fn imported_pagesize_1_is_refused_1339() {
    let err = module_code(IMPORTED_PAGESIZE_1).expect_err("this backend cannot lower (pagesize 1)");
    assert!(err.contains("(pagesize 1)"), "names the page size: {err}");
}
