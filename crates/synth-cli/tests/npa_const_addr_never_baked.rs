//! `--native-pointer-abi` never bakes a constant static address as a raw
//! linear-memory offset off R11.
//!
//! Under that ABI R11 is 0 (`CompileConfig::linear_memory_bytes`: "any
//! address beyond it is a runtime host pointer → `[R11=0 + addr]`"), so a
//! wasm static is reachable only through the `__synth_wasm_data + C`
//! relocation. Before this fix a constant address the selector did not
//! relocate was emitted as `movw rX,#addr; ldr [fp, rX]`, reading absolute
//! `addr`. In a module with no stack-pointer global that was every constant
//! address above the 0xFFF fold limit, and every constant address on the
//! i64 / float / bulk-memory arms. The i32 arms now fold and relocate any
//! static address; the other arms refuse loudly. The execution side (the
//! relocated objects run against wasmtime) is
//! `scripts/repro/npa_const_addr_differential.py`.

use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn wat_file(name: &str, wat: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("synth_npa_const_addr");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join(name);
    std::fs::write(&p, wat).expect("write wat");
    p
}

/// Compile with `--native-pointer-abi --relocatable`; return (success, the
/// object bytes when written, stdout+stderr). The output path is removed
/// first so a stale object can never be read as this run's.
fn compile(tag: &str, wat: &str, target: &str) -> (bool, Option<Vec<u8>>, String) {
    let src = wat_file(&format!("{tag}.wat"), wat);
    let out = src.with_extension("o");
    let _ = std::fs::remove_file(&out);
    let o = Command::new(synth())
        .args([
            "compile",
            src.to_str().unwrap(),
            "--target",
            target,
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
    let bytes = if o.status.success() {
        std::fs::read(&out).ok()
    } else {
        None
    };
    (o.status.success(), bytes, log)
}

/// Relocations in `.text` that target a linear-memory region symbol.
fn static_relocs(bytes: &[u8]) -> usize {
    use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};
    let obj = object::File::parse(bytes).expect("parse object");
    let text = obj.section_by_name(".text").expect(".text");
    text.relocations()
        .filter(|(_, r)| match r.target() {
            RelocationTarget::Symbol(i) => obj
                .symbol_by_index(i)
                .ok()
                .and_then(|s| s.name().ok().map(|n| n.starts_with("__synth_wasm_")))
                .unwrap_or(false),
            _ => false,
        })
        .count()
}

const SEGS: &str = r#"(memory (export "mem") 1)
  (data (i32.const 0x100) "\01\02\03\04\05\06\07\08")
  (data (i32.const 0x1000) "\11\12\13\14\15\16\17\18")
  (func (export "anchor") (result i32) (i32.load (i32.const 0x100)))"#;

const NEEDLE: &str = "which this lowering would emit as a raw linear-memory offset off R11";

/// i32 accesses at constant static addresses above the 0xFFF imm12 limit, in
/// a module with no stack-pointer global, are RELOCATED: every access
/// carries its own `__synth_wasm_*` relocation (pre-fix: only the folded
/// low anchor did, the rest were baked `[fp, rX]`).
#[test]
fn i32_const_addresses_above_the_fold_limit_are_relocated() {
    let wat = format!(
        r#"(module {SEGS}
  (func (export "ld") (result i32) (i32.load (i32.const 0x1004)))
  (func (export "ld8") (result i32) (i32.load8_u (i32.const 0x1007)))
  (func (export "ld_off") (result i32) (i32.load offset=0x1000 (i32.const 0)))
  (func (export "st") (i32.store (i32.const 0x1000) (i32.const 5)))
  (func (export "st16") (i32.store16 (i32.const 0x1002) (i32.const 5))))"#
    );
    let (ok, bytes, log) = compile("i32_high", &wat, "cortex-m3");
    assert!(ok, "must compile:\n{log}");
    assert_eq!(
        static_relocs(&bytes.expect("object")),
        6,
        "anchor + 5 high accesses must each carry a static-data relocation"
    );
}

/// Every arm that cannot fold a constant address refuses it, loudly, with
/// the precise reason, and writes no object.
#[test]
fn non_folding_arms_refuse_a_constant_static_address() {
    for (tag, target, body) in [
        (
            "i64_load",
            "cortex-m3",
            "(result i64) i32.const 0x1000 i64.load",
        ),
        (
            "i64_load_low",
            "cortex-m3",
            "(result i64) i32.const 0x100 i64.load",
        ),
        (
            "i64_store32",
            "cortex-m3",
            "i32.const 0x1000 i64.const 7 i64.store32",
        ),
        (
            "f32_store",
            "cortex-m7dp",
            "i32.const 0x1000 f32.const 1 f32.store",
        ),
        (
            "fill",
            "cortex-m3",
            "i32.const 0x1000 i32.const 9 i32.const 4 memory.fill",
        ),
        (
            "copy_dst",
            "cortex-m3",
            "i32.const 0x1000 i32.const 0x104 i32.const 4 memory.copy",
        ),
    ] {
        let wat = format!("(module {SEGS} (func (export \"f\") {body}))");
        let (ok, bytes, log) = compile(tag, &wat, target);
        assert!(
            !ok && bytes.is_none() && log.contains(NEEDLE),
            "{tag}: must be refused with the raw-offset diagnostic:\n{log}"
        );
    }
}

/// With a stack-pointer global, a constant at or above its init is already a
/// relocated pointer (`__synth_wasm_data + c`) — the i64 arm lowers it
/// correctly and must NOT be refused. Only the sliver where neither the
/// constant nor the offset is at/above the base, but their sum is, would
/// bake; there the i32 arm folds and the i64 arm refuses.
#[test]
fn stack_pointer_modules_refuse_only_the_sliver() {
    let wat = |body: &str| {
        format!(
            r#"(module (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x2000))
  (data (i32.const 0x2800) "\31\32\33\34\35\36\37\38")
  (func (export "f") {body}))"#
        )
    };
    let (ok, _, log) = compile(
        "sp_ptr_i64",
        &wat("(result i64) i32.const 0x2800 i64.load"),
        "cortex-m3",
    );
    assert!(
        ok,
        "a rewritten pointer constant must still compile:\n{log}"
    );
    let (ok, bytes, log) = compile(
        "sp_sliver_i32",
        &wat("(result i32) i32.const 0x1800 i32.load offset=0x1000"),
        "cortex-m3",
    );
    assert!(ok, "the sliver folds on the i32 arm:\n{log}");
    assert_eq!(static_relocs(&bytes.expect("object")), 1);
    let (ok, _, log) = compile(
        "sp_sliver_i64",
        &wat("(result i64) i32.const 0x1800 i64.load offset=0x1000"),
        "cortex-m3",
    );
    assert!(
        !ok && log.contains(NEEDLE),
        "the sliver on the i64 arm must be refused:\n{log}"
    );
}

/// RQ-89-NPARESIDUE (#1568), shape 1: a constant pointer routed through a
/// local that is read ONLY as the exact address of a scalar access is
/// relocated at its definition — each such access carries a static-data
/// relocation (pre-fix: none, the access read absolute `0x1004` off R11 = 0).
/// Executed against wasmtime by `scripts/repro/npa_const_addr_differential.py`.
#[test]
fn const_through_an_address_only_local_is_relocated() {
    let wat = format!(
        r#"(module {SEGS}
  (func (export "ld") (result i32) (local i32) i32.const 0x1004 local.set 0 local.get 0 i32.load)
  (func (export "tee") (result i32) (local i32) i32.const 0x1004 local.tee 0 i32.load)
  (func (export "st") (local i32) i32.const 0x1000 local.set 0 local.get 0 i32.const 5 i32.store)
  (func (export "ld64") (result i64) (local i32) i32.const 0x1000 local.set 0 local.get 0 i64.load))"#
    );
    let (ok, bytes, log) = compile("local_reloc", &wat, "cortex-m3");
    assert!(ok, "must compile:\n{log}");
    assert_eq!(
        static_relocs(&bytes.expect("object")),
        5,
        "anchor + 4 local-routed constant addresses must each carry a static-data relocation"
    );
}

/// Shape 1, the refusals: a local-routed constant address the plan cannot
/// relocate soundly is refused loudly on EVERY arm (the i32 fold only sees a
/// positional `i32.const`), one row per relocation condition.
#[test]
fn const_through_a_local_that_cannot_be_relocated_is_refused() {
    for (tag, body) in [
        (
            "nonzero_offset",
            "(result i32) (local i32) i32.const 5 local.set 0 local.get 0 i32.load8_u offset=0x1000",
        ),
        (
            "zero_init_visible",
            "(result i32) (local i32) block i32.const 0x1004 local.set 0 end local.get 0 i32.load",
        ),
        (
            "scalar_observer",
            "(result i32) (local i32) i32.const 0x1004 local.set 0 local.get 0 i32.load local.get 0 i32.add",
        ),
    ] {
        let wat = format!("(module {SEGS} (func (export \"f\") {body}))");
        let (ok, bytes, log) = compile(tag, &wat, "cortex-m3");
        assert!(
            !ok && bytes.is_none() && log.contains(NEEDLE) && log.contains("local 0"),
            "{tag}: must be refused with the raw-offset diagnostic naming the local:\n{log}"
        );
    }
}

/// With a stack-pointer global a pointer constant routed through a local is
/// already relocated at its definition (the #237 rule) and must still
/// compile; the sliver routed through a local is refused.
#[test]
fn stack_pointer_modules_relocate_a_local_pointer_and_refuse_the_local_sliver() {
    let wat = |body: &str| {
        format!(
            r#"(module (memory (export "mem") 1)
  (global $sp (mut i32) (i32.const 0x2000))
  (data (i32.const 0x2800) "\31\32\33\34\35\36\37\38")
  (func (export "f") {body}))"#
        )
    };
    let (ok, _, log) = compile(
        "sp_local_ptr",
        &wat("(result i32) (local i32) i32.const 0x2804 local.set 0 local.get 0 i32.load"),
        "cortex-m3",
    );
    assert!(
        ok,
        "a rewritten pointer constant through a local must compile:\n{log}"
    );
    let (ok, bytes, log) = compile(
        "sp_local_sliver",
        &wat(
            "(result i32) (local i32) i32.const 0x1800 local.set 0 local.get 0 i32.load offset=0x1000",
        ),
        "cortex-m3",
    );
    assert!(
        !ok && bytes.is_none() && log.contains(NEEDLE),
        "the sliver through a local must be refused:\n{log}"
    );
}
