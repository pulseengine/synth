//! #1580: under `--native-pointer-abi` WITH a stack-pointer global, a
//! constant address plus a non-zero memarg offset is relocated on its
//! EFFECTIVE address, so the mixed split retargets it to the data region that
//! holds `C + offset` — never to the region holding `C` (wrong region) and
//! never with both parts relocated (doubled address). A constant reached
//! through a LOCAL whose offset moves the access into another region is
//! refused. The execution side is
//! `scripts/repro/npa_offset_cross_segment_1580_differential.py`.

use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn compile(tag: &str, wat: &str) -> (bool, Option<Vec<u8>>, String) {
    let dir = std::env::temp_dir().join("synth_npa_offset_1580");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let src: PathBuf = dir.join(format!("{tag}.wat"));
    std::fs::write(&src, wat).expect("write wat");
    let out = src.with_extension("o");
    let _ = std::fs::remove_file(&out);
    let o = Command::new(synth())
        .args([
            "compile",
            src.to_str().unwrap(),
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--native-pointer-abi",
            "-o",
            out.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");
    let log = format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    );
    let bytes = o
        .status
        .success()
        .then(|| std::fs::read(&out).ok())
        .flatten();
    (o.status.success(), bytes, log)
}

/// `(symbol, in-place REL addend)` of every `.text` relocation against a
/// linear-memory region symbol.
fn static_relocs(bytes: &[u8]) -> Vec<(String, u32)> {
    use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};
    let obj = object::File::parse(bytes).expect("parse object");
    let text = obj.section_by_name(".text").expect(".text");
    let data = text.data().expect(".text data");
    text.relocations()
        .filter_map(|(off, r)| {
            let RelocationTarget::Symbol(i) = r.target() else {
                return None;
            };
            let name = obj.symbol_by_index(i).ok()?.name().ok()?.to_string();
            let o = off as usize;
            let addend = u32::from_le_bytes(data[o..o + 4].try_into().unwrap());
            name.starts_with("__synth_wasm_").then_some((name, addend))
        })
        .collect()
}

const HDR: &str = r#"(module (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x800))
  (data (i32.const 0x900) "\aa\bb\cc\dd")
  (data (i32.const 0x2000) "\31\32\33\34\35\36\37\38")"#;

/// The issue's `x` (both parts relocatable) and `y` (only `C`) each carry
/// exactly ONE static relocation, to `__synth_wasm_seg_1 + 4` — the region
/// holding the effective address 0x2004. Pre-fix: `y` was
/// `__synth_wasm_data + 0x1900` (the zero reservation) and `x` carried
/// `__synth_wasm_seg_0 + 0` PLUS `__synth_wasm_data + 0x1704`.
#[test]
fn constant_plus_offset_is_relocated_on_the_effective_address() {
    for (tag, body) in [
        ("x", "i32.const 0x900 i32.load offset=0x1704"),
        ("y", "i32.const 0x1900 i32.load offset=0x704"),
        ("y64", "i32.const 0x1900 i64.load32_u offset=0x704"),
        (
            "st",
            "i32.const 0x1900 i32.const 7 i32.store offset=0x704 i32.const 0",
        ),
    ] {
        let wat = format!("{HDR}\n  (func (export \"f\") (result i32) {body}))");
        let (ok, bytes, log) = compile(&format!("eff_{tag}"), &wat);
        assert!(ok, "{tag}: must compile:\n{log}");
        assert_eq!(
            static_relocs(&bytes.expect("object")),
            vec![("__synth_wasm_seg_1".to_string(), 4)],
            "{tag}: exactly one relocation, on the effective address 0x2004"
        );
    }
}

/// Through a local the offset cannot be folded into the shared definition:
/// leaving the constant's region is refused with the #1580 diagnostic and no
/// object; staying inside it (a field off a static base, the #757 shape)
/// compiles.
#[test]
fn constant_through_a_local_leaving_its_region_is_refused() {
    let leave = format!(
        "{HDR}\n  (func (export \"f\") (result i32) (local i32) i32.const 0x900 \
         local.set 0 local.get 0 i32.load offset=0x1704))"
    );
    let (ok, bytes, log) = compile("local_leave", &leave);
    assert!(!ok, "must be refused:\n{log}");
    assert!(bytes.is_none(), "no object on a refusal");
    assert!(
        log.contains("(#1580)") && log.contains("through local 0"),
        "refused for the wrong reason:\n{log}"
    );
    let stay = format!(
        "{HDR}\n  (func (export \"f\") (result i32) (local i32) i32.const 0x2000 \
         local.set 0 local.get 0 i32.load offset=4))"
    );
    let (ok, _, log) = compile("local_stay", &stay);
    assert!(
        ok,
        "an offset inside the constant's own region must compile:\n{log}"
    );
}
