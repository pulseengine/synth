//! #686 — `SYNTH_SHIFT_MASK_ELIDE`: elide the #682 mod-32 shift-amount mask
//! when the amount is statically provable < 32.
//!
//! Three gates, per the flag-then-flip protocol:
//!
//! 1. **Default is OFF and byte-identical to baseline** — the elision moves
//!    the frozen anchors (const-amount shifts fold back to the immediate
//!    form), so it lands opt-in. `frozen_codegen_bytes.rs` locks the shipped
//!    bytes; this test additionally pins unset ≡ explicit opt-out, so the
//!    default can only change via a deliberate flip (which updates this).
//! 2. **Per-function no-grow table** — with the flag ON, no function in the
//!    corpus gets BIGGER on either path (relocatable/direct and default/
//!    optimized). Elision is removal/rewrite-only; growth would mean the
//!    pass leaked somewhere it doesn't understand.
//! 3. **gust_mix recovers the #682 size regression** — the gale-measured
//!    fixture (`gust_mix_686.wat`, constant Q8 shift) must strictly shrink:
//!    the `movw + and r12 + shift.w` triple folds to the immediate shift.
//!    (The 12% is cycles on silicon; bytes are the buildable proxy — the
//!    10 B here is exactly the dead mask + dead materialization.)
//!
//! Result-correctness for the elision (including amounts >= 32, where it
//! must never fire) is owned by `scripts/repro/i32_shift_mask_682_differential.py`
//! — re-run green with the flag ON at land time, and red-tested against a
//! force-elide of a >= 32 case (10 rows red, both paths).

use std::collections::BTreeMap;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// The ARM corpus the frozen byte-gate pins, plus the two shift fixtures.
const CORPUS: &[&str] = &[
    "control_step.wasm",
    "flight_seam.wasm",
    "flight_seam_flat.wasm",
    "signed_div_const.wasm",
    "i32_shift_mask_682.wat",
    "gust_mix_686.wat",
];

/// Both codegen paths: `--relocatable` forces the direct stack selector; the
/// default is the optimized bridge. The #682 mask (and therefore the #686
/// elision) exists on both.
const VARIANTS: &[(&str, bool)] = &[("relocatable", true), ("default", false)];

/// Compile `wasm` and return (.text bytes, per-function sizes by symbol name).
/// Sizes are derived from sorted symbol addresses (next symbol / section end),
/// the same symtab the `.py` differentials read — `st_size` is not populated.
fn compile(wasm: &str, relocatable: bool, elide: Option<&str>) -> (Vec<u8>, BTreeMap<String, u64>) {
    let path = fixture(wasm);
    let elf = format!(
        "/tmp/shift_mask_elide_686_{}_{}_{}.o",
        wasm.replace('.', "_"),
        relocatable,
        elide.unwrap_or("unset")
    );
    let mut cmd = Command::new(synth());
    cmd.env_remove("SYNTH_SHIFT_MASK_ELIDE");
    if let Some(v) = elide {
        cmd.env("SYNTH_SHIFT_MASK_ELIDE", v);
    }
    cmd.args([
        "compile",
        path.to_str().unwrap(),
        "-o",
        &elf,
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--all-exports",
    ]);
    if relocatable {
        cmd.arg("--relocatable");
    }
    let out = cmd.output().expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed for {wasm} (relocatable={relocatable}): {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    let text = obj.section_by_name(".text").expect(".text");
    let data = text.data().expect("read .text").to_vec();
    let end = text.address() + data.len() as u64;

    // Function starts: named symbols inside .text, sorted by address.
    let mut starts: Vec<(u64, String)> = obj
        .symbols()
        .filter(|s| {
            !s.name().unwrap_or("").is_empty()
                && matches!(
                    s.kind(),
                    SymbolKind::Text | SymbolKind::Label | SymbolKind::Unknown
                )
                && s.address() >= text.address()
                && s.address() < end
        })
        .map(|s| (s.address(), s.name().unwrap().to_string()))
        .collect();
    starts.sort();
    starts.dedup_by(|a, b| a.0 == b.0); // aliases (func_N + export name) — keep one
    let mut sizes = BTreeMap::new();
    for (i, (addr, name)) in starts.iter().enumerate() {
        let next = starts.get(i + 1).map(|(a, _)| *a).unwrap_or(end);
        sizes.insert(name.clone(), next - addr);
    }
    (data, sizes)
}

/// Gate 1: unset ≡ `SYNTH_SHIFT_MASK_ELIDE=0`, byte-for-byte — the flag is
/// opt-in. A deliberate default-on flip re-freezes the anchors and updates
/// this assertion (flag-then-flip protocol; the maintainer owns the flip).
#[test]
fn shift_mask_elide_686_default_is_off_and_byte_identical() {
    for &(vname, reloc) in VARIANTS {
        for &wasm in CORPUS {
            let (unset, _) = compile(wasm, reloc, None);
            let (off, _) = compile(wasm, reloc, Some("0"));
            assert_eq!(
                unset, off,
                "{wasm} [{vname}]: default must equal explicit opt-out (flag is opt-in)"
            );
        }
    }
}

/// Gates 2+3: per-function no-grow across the corpus, strict shrink on the
/// gale-measured gust_mix shape (and the #682 const-amount repro functions).
#[test]
fn shift_mask_elide_686_per_function_no_grow_and_gust_mix_recovers() {
    for &(vname, reloc) in VARIANTS {
        for &wasm in CORPUS {
            let (off_bytes, off) = compile(wasm, reloc, Some("0"));
            let (on_bytes, on) = compile(wasm, reloc, Some("1"));
            assert_eq!(
                off.keys().collect::<Vec<_>>(),
                on.keys().collect::<Vec<_>>(),
                "{wasm} [{vname}]: the flag must not add/drop functions"
            );
            for (name, off_size) in &off {
                let on_size = on[name];
                assert!(
                    on_size <= *off_size,
                    "{wasm} [{vname}] {name}: GREW under elision ({off_size} -> {on_size} B) \
                     — the pass is removal/rewrite-only, growth is a leak"
                );
            }
            assert!(
                on_bytes.len() <= off_bytes.len(),
                "{wasm} [{vname}]: .text grew under elision"
            );
        }
    }

    // gust_mix: the Q8 constant shift's masked triple must fold — this is the
    // fixture whose +14 B / +12% gale measured on #682's unconditional mask.
    for &(vname, reloc) in VARIANTS {
        let (off_bytes, _) = compile("gust_mix_686.wat", reloc, Some("0"));
        let (on_bytes, _) = compile("gust_mix_686.wat", reloc, Some("1"));
        assert!(
            on_bytes.len() < off_bytes.len(),
            "gust_mix [{vname}]: elision must strictly shrink the constant-shift \
             function ({} -> {} B)",
            off_bytes.len(),
            on_bytes.len()
        );
    }

    // The #682 repro's const-amount functions (shl32/shl33/shl300/shr300/
    // sar300) all fold mod 32 on the direct path — strict shrink there too.
    let (off_bytes, _) = compile("i32_shift_mask_682.wat", true, Some("0"));
    let (on_bytes, _) = compile("i32_shift_mask_682.wat", true, Some("1"));
    assert!(
        on_bytes.len() < off_bytes.len(),
        "i32_shift_mask_682 [relocatable]: const >= 32 amounts must now fold mod 32 \
         ({} -> {} B)",
        off_bytes.len(),
        on_bytes.len()
    );
}
