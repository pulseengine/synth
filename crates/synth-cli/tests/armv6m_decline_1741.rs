//! RQ-92-WDGTHIN (Refs #1741, #1301): the named loud-decline tripwires of the
//! ARMv6-M backend (`--target cortex-m0` / `cortex-m0plus`).
//!
//! ARMv6-M lowers the i32 core, structured control flow and direct calls.
//! Everything else it REFUSES, and this file pins what "refuses" means for
//! each shape, on both targets, with the shipped `synth` binary:
//!
//! - the function is absent from the object (read back from the ELF symbol
//!   table), while a lowered function of the same module is present — a
//!   decline is per function, not a failed compile mistaken for one;
//! - the diagnostic names the function and the cause ([`DECLINES`]);
//! - without `--allow-skipped-exports` the compile exits non-zero (#952), so
//!   a build gating on `$?` cannot ship an object missing an export;
//! - the set is EXACT both ways: a shape that starts compiling reds here, and
//!   must arrive with an execution oracle (`crates/synth-oracle/tests/
//!   armv6m_i32_oracle.rs`, `armv6m_call_oracle.rs`) before this list moves.
//!
//! The whole-compile refusals are pinned too: a self-contained ARMv6-M image
//! (no vector table or startup code is checked against ARMv6-M) and a
//! non-ARM backend.
//!
//! WHAT THIS DOES NOT SHOW: that every unsupported shape declines. It shows
//! that these named ones do. The fail-closed mechanism behind the list is
//! the lowering's rule table (an op with no rule is refused by name) and the
//! byte check on every encoded instruction (`synth_backend::armv6m`).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use object::{Object, ObjectSymbol};

const TARGETS: &[&str] = &["cortex-m0", "cortex-m0plus"];

const WAT: &str = r#"(module
  (import "env" "five" (func $five (param i32 i32 i32 i32 i32) (result i32)))
  (import "env" "wide" (func $wide (param i64) (result i32)))
  (type $t (func (param i32) (result i32)))
  (table 1 funcref)
  (memory 1)
  (global $g (mut i32) (i32.const 3))
  (func (export "ok_add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "d_div_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_u)
  (func (export "d_div_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_s)
  (func (export "d_rem_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rem_u)
  (func (export "d_rem_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rem_s)
  (func (export "d_clz") (param i32) (result i32) local.get 0 i32.clz)
  (func (export "d_ctz") (param i32) (result i32) local.get 0 i32.ctz)
  (func (export "d_popcnt") (param i32) (result i32) local.get 0 i32.popcnt)
  (func (export "d_i64_add") (param i64 i64) (result i64) local.get 0 local.get 1 i64.add)
  (func (export "d_i64_mul") (param i64 i64) (result i64) local.get 0 local.get 1 i64.mul)
  (func (export "d_i64_lt_s") (param i64 i64) (result i32) local.get 0 local.get 1 i64.lt_s)
  (func (export "d_i64_shl") (param i64 i64) (result i64) local.get 0 local.get 1 i64.shl)
  (func (export "d_load") (param i32) (result i32) local.get 0 i32.load)
  (func (export "d_load8") (param i32) (result i32) local.get 0 i32.load8_u)
  (func (export "d_store") (param i32 i32) local.get 0 local.get 1 i32.store)
  (func (export "d_global_get") (result i32) global.get $g)
  (func (export "d_global_set") (param i32) local.get 0 global.set $g)
  (func (export "d_memory_size") (result i32) memory.size)
  (func (export "d_memory_grow") (param i32) (result i32) local.get 0 memory.grow)
  (func (export "d_params5") (param i32 i32 i32 i32 i32) (result i32) local.get 0 local.get 4 i32.add)
  (func (export "d_call_indirect") (param i32) (result i32) local.get 0 i32.const 0 call_indirect (type $t))
  (func (export "d_stack_arg") (param i32) (result i32)
    local.get 0 local.get 0 local.get 0 local.get 0 local.get 0 call $five)
  (func (export "d_i64_arg") (param i64) (result i32) local.get 0 call $wide)
  (func (export "d_f32_add") (param f32 f32) (result f32) local.get 0 local.get 1 f32.add)
  (func (export "d_f32_param") (param f32) (result f32) local.get 0)
  (func (export "d_f64_const") (result f64) f64.const 1.5)
)
"#;

/// Every export that must decline, and what its diagnostic must say.
const V6M: &str = "ARMv6-M lowering, RQ-91-M0I32 (#1301)";
const DECLINES: &[(&str, &[&str])] = &[
    ("d_div_u", &[V6M, "no ARMv6-M rule for `Udiv"]),
    ("d_div_s", &[V6M, "no ARMv6-M rule for"]),
    ("d_rem_u", &[V6M, "no ARMv6-M rule for `Udiv"]),
    ("d_rem_s", &[V6M, "no ARMv6-M rule for `Sdiv"]),
    ("d_clz", &[V6M, "no ARMv6-M rule for `Clz"]),
    ("d_ctz", &[V6M, "no ARMv6-M rule for `Rbit"]),
    ("d_popcnt", &[V6M, "no ARMv6-M rule for `Popcnt"]),
    ("d_i64_add", &[V6M, "no ARMv6-M rule for `Adds"]),
    ("d_i64_mul", &[V6M, "no ARMv6-M rule for `I64Mul"]),
    ("d_i64_lt_s", &[V6M, "no ARMv6-M rule for `I64SetCond"]),
    ("d_i64_shl", &[V6M, "no ARMv6-M rule for `I64Shl"]),
    ("d_load", &[V6M, "names R11 (globals / linear memory)"]),
    ("d_load8", &[V6M, "names R11 (globals / linear memory)"]),
    ("d_store", &[V6M, "names R11 (globals / linear memory)"]),
    ("d_global_get", &[V6M, "names R9 (globals / linear memory)"]),
    ("d_global_set", &[V6M, "names R9 (globals / linear memory)"]),
    ("d_memory_size", &[V6M, "no ARMv6-M rule for `MemorySize"]),
    ("d_memory_grow", &[V6M, "no ARMv6-M rule for `MemoryGrow"]),
    ("d_params5", &[V6M, "reads an incoming stack argument"]),
    (
        "d_call_indirect",
        &[V6M, "no ARMv6-M rule for `CallIndirect"],
    ),
    (
        "d_stack_arg",
        &[V6M, "passes 5 arguments", "outgoing stack argument"],
    ),
    // Refused on every ARM target, ARMv6-M included (#929).
    ("d_i64_arg", &["#929: call arg 0 is 64-bit"]),
    // No FPU: refused by the selector, naming the ARMv6-M triple.
    (
        "d_f32_add",
        &["GI-FPU-002", "'thumbv6m-none-eabi' has none"],
    ),
    (
        "d_f32_param",
        &["GI-FPU-002", "'thumbv6m-none-eabi' has none"],
    ),
    (
        "d_f64_const",
        &["GI-FPU-002", "'thumbv6m-none-eabi' has no FPU"],
    ),
];

fn dir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!(
        "synth_armv6m_decline_1741_{}_{tag}",
        std::process::id()
    ));
    std::fs::create_dir_all(&d).expect("mkdir");
    d
}

fn synth(input: &Path, out: &Path, flags: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_synth"))
        .args([
            "compile",
            input.to_str().unwrap(),
            "-o",
            out.to_str().unwrap(),
        ])
        .args(flags)
        .env("RUST_LOG", "error")
        .output()
        .expect("run synth")
}

fn defined_symbols(elf: &Path) -> BTreeSet<String> {
    let bytes = std::fs::read(elf).expect("object written");
    let file = object::File::parse(&*bytes).expect("ELF");
    file.symbols()
        .filter(|s| !s.is_undefined())
        .filter_map(|s| s.name().ok().map(str::to_string))
        .collect()
}

#[test]
fn every_unsupported_shape_declines_by_name_on_cortex_m0_and_m0plus() {
    for target in TARGETS {
        let d = dir(target);
        let wat = d.join("declines.wat");
        std::fs::write(&wat, WAT).unwrap();
        let out = d.join("declines.o");
        let run = synth(
            &wat,
            &out,
            &[
                "--target",
                target,
                "--relocatable",
                "--all-exports",
                "--allow-skipped-exports",
                "--embedder-global-init",
            ],
        );
        let stderr = String::from_utf8_lossy(&run.stderr).into_owned();
        assert!(run.status.success(), "{target}: {stderr}");

        // EXACT both ways, from the diagnostics.
        let skipped: BTreeSet<String> = stderr
            .lines()
            .filter_map(|l| l.strip_prefix("warning: skipping function '"))
            .filter_map(|l| l.split('\'').next())
            .map(str::to_string)
            .collect();
        let want: BTreeSet<String> = DECLINES.iter().map(|(n, _)| n.to_string()).collect();
        assert_eq!(
            skipped,
            want,
            "{target}: the declined set moved (now declined {:?}, no longer declined {:?})",
            skipped.difference(&want).collect::<Vec<_>>(),
            want.difference(&skipped).collect::<Vec<_>>()
        );
        for (name, causes) in DECLINES {
            let line = stderr
                .lines()
                .find(|l| l.starts_with(&format!("warning: skipping function '{name}'")))
                .unwrap();
            for cause in *causes {
                assert!(
                    line.contains(cause),
                    "{target}: {name} declined, but not for `{cause}`: {line}"
                );
            }
        }

        // And from the object: the lowered function is there, no declined
        // one is.
        let syms = defined_symbols(&out);
        assert!(
            syms.contains("ok_add"),
            "{target}: ok_add missing: {syms:?}"
        );
        for (name, _) in DECLINES {
            assert!(
                !syms.contains(*name),
                "{target}: declined function {name} is in the object"
            );
        }

        // #952: a declined export is a hard refusal without the escape hatch.
        let strict = synth(
            &wat,
            &d.join("strict.o"),
            &[
                "--target",
                target,
                "--relocatable",
                "--all-exports",
                "--embedder-global-init",
            ],
        );
        assert!(
            !strict.status.success(),
            "{target}: a module with declined exports compiled at exit 0"
        );
        assert!(
            String::from_utf8_lossy(&strict.stderr).contains("#952"),
            "{target}: the refusal does not name #952"
        );
        let _ = std::fs::remove_dir_all(&d);
    }
}

#[test]
fn armv6m_refuses_a_self_contained_image_and_a_non_arm_backend() {
    let leaf = "(module (func (export \"f\") (param i32) (result i32) local.get 0))";
    for target in TARGETS {
        let d = dir(&format!("shape-{target}"));
        let wat = d.join("leaf.wat");
        std::fs::write(&wat, leaf).unwrap();
        // Every invocation that would build a self-contained image.
        for flags in [
            &["--target", target][..],
            &["--target", target, "--all-exports"][..],
            &["--target", target, "-n", "f"][..],
        ] {
            let out = d.join("image.elf");
            let run = synth(&wat, &out, flags);
            let stderr = String::from_utf8_lossy(&run.stderr).into_owned();
            assert!(
                !run.status.success(),
                "{flags:?}: a self-contained ARMv6-M image compiled"
            );
            assert!(
                stderr.contains("ARMv6-M")
                    && stderr.contains("supports only `--relocatable` objects"),
                "{flags:?}: {stderr}"
            );
            assert!(!out.exists(), "{flags:?}: an output file was written");
        }
        // CONTROL: the relocatable object compiles.
        let ok = synth(
            &wat,
            &d.join("leaf.o"),
            &["--target", target, "--relocatable"],
        );
        assert!(
            ok.status.success(),
            "{target}: {}",
            String::from_utf8_lossy(&ok.stderr)
        );
        // A backend that does not run the ARMv6-M instruction check.
        let other = synth(
            &wat,
            &d.join("w2c2.o"),
            &["--target", target, "--relocatable", "-b", "w2c2"],
        );
        let stderr = String::from_utf8_lossy(&other.stderr).into_owned();
        assert!(!other.status.success());
        assert!(
            stderr.contains("only available with the ARM backend"),
            "{target}: {stderr}"
        );
        let _ = std::fs::remove_dir_all(&d);
    }
}
