//! RQ-89-PAGESIZEAPI (#1339): the RV32 backend's `memory.size` lowering is
//! `li rd, bytes / 65536`, so a `(pagesize 1)` memory of 20000 bytes answered
//! 0 where wasmtime answers 20000 — through the published `Backend` API on
//! every path, AND through `synth compile -b riscv --relocatable`, whose CLI
//! refusal honoured `(pagesize 1)` on `--relocatable` for every backend
//! although only the ARM lowering reads the declared page size (#1441). The
//! backend now refuses it loudly, naming the page size.

use synth_backend_riscv::RiscVBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::target::TargetSpec;
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

fn cfg(relocatable: bool) -> CompileConfig {
    CompileConfig {
        target: TargetSpec::riscv32imac(),
        relocatable,
        ..CompileConfig::default()
    }
}

#[test]
fn compile_module_refuses_pagesize_1_1339() {
    let module = decode_wasm_module(PAGESIZE_1).expect("decodes");
    for relocatable in [false, true] {
        let err = RiscVBackend
            .compile_module(&module, &cfg(relocatable))
            .map(|_| ())
            .expect_err("RV32 cannot lower memory.size for (pagesize 1)")
            .to_string();
        assert!(err.contains("(pagesize 1)"), "names the page size: {err}");
        assert!(err.contains("#1339"), "cites the analysis: {err}");
    }
}

#[test]
fn compile_function_refuses_a_byte_paged_config_1339() {
    let module = decode_wasm_module(PAGESIZE_1).expect("decodes");
    let f = &module.functions[0];
    let err = RiscVBackend
        .compile_function(
            "ms",
            &f.ops,
            &CompileConfig {
                memory0_page_log2: 0,
                linear_memory_bytes: 20000,
                ..cfg(true)
            },
        )
        .map(|_| ())
        .expect_err("a byte-paged config must be refused")
        .to_string();
    assert!(err.contains("(pagesize 1)"), "names the page size: {err}");
}

#[test]
fn default_page_size_still_compiles_1339() {
    let module = decode_wasm_module(DEFAULT_PAGE).expect("decodes");
    for relocatable in [false, true] {
        RiscVBackend
            .compile_module(&module, &cfg(relocatable))
            .expect("default page compiles");
    }
}
