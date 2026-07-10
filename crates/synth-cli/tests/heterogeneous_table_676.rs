//! #676 — heterogeneous funcref tables: runtime type check + type-id sidecar.
//!
//! The cargo-visible complement to `scripts/repro/call_indirect_676_differential.py`
//! (which needs wasmtime + unicorn and runs in the isolated CI differential
//! job). Locks the OBJECT-level contract:
//!
//!  - a module with a heterogeneous table COMPILES (pre-#676 every
//!    `call_indirect` through it loud-declined and the dispatcher symbols
//!    were missing) and its object carries the `.synth.table_type_ids`
//!    sidecar — one LE u32 structural class id per slot, region order,
//!    id 0 = null slot, structural duplicates sharing one id;
//!  - a homogeneous module emits NO sidecar section — its object stays
//!    byte-identical by construction (the `.text` half of that pin lives in
//!    `frozen_codegen_bytes.rs`).
//!
//! Both ISAs of the expansion (Thumb-2 `cortex-m3`, A32 `cortex-r5`).

use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// Compile a fixture with the exact config the `.py` differentials use and
/// return the parsed object bytes.
fn compile(wasm: &str, target: &str) -> Vec<u8> {
    let path = fixture(wasm);
    let elf = format!("/tmp/hetero676_{target}_{wasm}.o");
    let out = Command::new(synth())
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            &elf,
            "--target",
            target,
            "--all-exports",
            "--relocatable",
            "--no-optimize",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed for {wasm} ({target}): {}",
        String::from_utf8_lossy(&out.stderr)
    );
    std::fs::read(&elf).expect("read object")
}

/// #676: the heterogeneous fixture compiles (no decline) and the object
/// carries the type-id sidecar with the expected structural class ids.
#[test]
fn test_676_heterogeneous_table_compiles_with_sidecar() {
    for target in ["cortex-m3", "cortex-r5"] {
        let bytes = compile("call_indirect_676_heterogeneous.wat", target);
        let obj = object::File::parse(&*bytes).expect("parse object");

        // Pre-#676 red: the dispatchers loud-declined → symbols missing.
        for need in ["via2", "via1", "func_0", "func_1", "func_2"] {
            assert!(
                obj.symbols().any(|s| s.name() == Ok(need)),
                "{target}: symbol {need} missing — the dispatch declined (#676)"
            );
        }

        // The sidecar: slots [$add(bin), $neg(un), $sub(bin2 ≡ bin), null,
        // null] → class ids [1, 2, 1, 0, 0] ($bin2 is a structural duplicate
        // of $bin — one id; 0 is the reserved null id).
        let sidecar = obj
            .section_by_name(".synth.table_type_ids")
            .unwrap_or_else(|| panic!("{target}: .synth.table_type_ids section missing (#676)"));
        let data = sidecar.data().expect("sidecar data");
        let ids: Vec<u32> = data
            .chunks_exact(4)
            .map(|w| u32::from_le_bytes(w.try_into().unwrap()))
            .collect();
        assert_eq!(
            ids,
            vec![1, 2, 1, 0, 0],
            "{target}: sidecar class ids (structural dedup + null id 0)"
        );
    }
}

/// #676 by-construction pin: homogeneous modules (the frozen #642/#650/#664
/// fixtures) emit NO sidecar section — nothing about their objects changes.
#[test]
fn test_676_homogeneous_fixtures_emit_no_sidecar() {
    for wasm in [
        "call_indirect_642_oob.wat",
        "call_indirect_650_multitable.wat",
        "call_indirect_664_nullslot.wat",
    ] {
        for target in ["cortex-m3", "cortex-r5"] {
            let bytes = compile(wasm, target);
            let obj = object::File::parse(&*bytes).expect("parse object");
            assert!(
                obj.section_by_name(".synth.table_type_ids").is_none(),
                "{wasm} ({target}): homogeneous module must emit no sidecar (#676)"
            );
        }
    }
}
