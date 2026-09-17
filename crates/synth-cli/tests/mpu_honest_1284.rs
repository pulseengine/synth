//! RQ-68-MPUHONEST (#1284, #1145) — `--safety-bounds mpu` is accepted only
//! where it is honest.
//!
//! synth emits NO MPU or PMP programming on any path. Before v0.68 `mpu` (and
//! its undocumented alias `pmp`) was accepted everywhere and produced bytes
//! identical to `none` with no warning — a silent no-op on a memory-safety
//! control. The contract, set with gale on #1145:
//!
//! | shape                                              | verdict                      |
//! |----------------------------------------------------|------------------------------|
//! | ARM self-contained (`--cortex-m`, plain `--all-exports`, untargeted) | refuse |
//! | ARM single-function path                           | refuse (synth-owned image)   |
//! | ARM relocatable, no `--embedder-mpu`               | refuse                       |
//! | ARM relocatable + `--embedder-mpu`                 | accept, bytes == `none`      |
//! | multi-memory relocatable + `--embedder-mpu`        | accept, bytes == plain       |
//! | RV32 `mpu` / `pmp`, any path                       | refuse                       |
//! | `pmp` on ARM                                       | refuse (never an alias)      |
//! | `--embedder-mpu` without `--safety-bounds mpu`     | refuse (meaningless)         |

use std::path::{Path, PathBuf};
use std::process::Command;

mod artifact_guard;

const ONE_MEM: &str = r#"(module (memory (export "memory") 1)
  (func (export "load") (param i32) (result i32) (i32.load (local.get 0)))
  (func (export "store") (param i32 i32) (i32.store (local.get 0) (local.get 1))))"#;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn one_mem_fixture() -> PathBuf {
    let dir = std::env::temp_dir().join("synth_mpu_honest_1284");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join("one_mem.wat");
    std::fs::write(&p, ONE_MEM).expect("write wat");
    p
}

fn two_tenant_fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/mem_isolation_two_tenant_1145.wat")
}

/// Run a compile that is expected to be REFUSED; returns (success, stderr).
fn run(input: &Path, tag: &str, extra: &[&str]) -> (bool, String) {
    let out = artifact_guard::unique_artifact(&format!("mpu1284_{tag}"), "o");
    let o = Command::new(synth())
        .arg("compile")
        .arg(input)
        .arg("-o")
        .arg(&out)
        .args(extra)
        .output()
        .expect("run synth");
    (
        o.status.success(),
        String::from_utf8_lossy(&o.stderr).into_owned(),
    )
}

/// Compile and return THIS invocation's object bytes (artifact_guard).
fn bytes(input: &Path, tag: &str, extra: &[&str]) -> (Vec<u8>, PathBuf) {
    let out = artifact_guard::unique_artifact(&format!("mpu1284_{tag}"), "o");
    let mut cmd = Command::new(synth());
    cmd.arg("compile").arg(input).arg("-o").arg(&out).args(extra);
    (
        artifact_guard::compile_bytes_or_panic(&mut cmd, &out, tag),
        out,
    )
}

fn assert_refused(input: &Path, tag: &str, extra: &[&str], needles: &[&str]) {
    let (ok, err) = run(input, tag, extra);
    assert!(!ok, "{tag}: expected a refusal, got success. stderr: {err}");
    for n in needles {
        assert!(err.contains(n), "{tag}: refusal does not mention {n:?}: {err}");
    }
}

#[test]
fn self_contained_arm_refuses_mpu_1284() {
    let f = one_mem_fixture();
    for (tag, extra) in [
        ("cortex_m", vec!["--cortex-m", "--safety-bounds", "mpu"]),
        (
            "all_exports",
            vec!["--target", "cortex-m3", "--all-exports", "--safety-bounds", "mpu"],
        ),
        ("untargeted", vec!["--safety-bounds", "mpu"]),
    ] {
        assert_refused(
            &f,
            tag,
            &extra,
            &["self-contained ARM image", "NO MPU programming", "#1145"],
        );
    }
}

#[test]
fn single_function_path_refuses_mpu_even_with_the_flag_1284() {
    assert_refused(
        &one_mem_fixture(),
        "single_func",
        &[
            "--func-index",
            "0",
            "--relocatable",
            "--safety-bounds",
            "mpu",
            "--embedder-mpu",
        ],
        &["single-function path", "#1145"],
    );
}

#[test]
fn riscv_refuses_mpu_and_pmp_on_every_path_1284() {
    let f = one_mem_fixture();
    assert_refused(
        &f,
        "rv_mpu",
        &["-b", "riscv", "--all-exports", "--safety-bounds", "mpu"],
        &["RISC-V backend", "no", "PMP programming", "#1145"],
    );
    assert_refused(
        &f,
        "rv_mpu_reloc",
        &[
            "-b",
            "riscv",
            "--all-exports",
            "--relocatable",
            "--safety-bounds",
            "mpu",
        ],
        &["RISC-V backend", "#1145"],
    );
    assert_refused(
        &f,
        "rv_pmp",
        &["-b", "riscv", "--all-exports", "--safety-bounds", "pmp"],
        &["--safety-bounds pmp is refused", "#1145"],
    );
}

#[test]
fn pmp_is_never_an_alias_on_arm_1284() {
    assert_refused(
        &one_mem_fixture(),
        "arm_pmp",
        &[
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--safety-bounds",
            "pmp",
            "--embedder-mpu",
        ],
        &["--safety-bounds pmp is refused", "never a silent alias"],
    );
}

#[test]
fn relocatable_mpu_without_the_acknowledgment_is_refused_1284() {
    assert_refused(
        &one_mem_fixture(),
        "reloc_noflag",
        &[
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--safety-bounds",
            "mpu",
        ],
        &["requires --embedder-mpu", "docs/embedder-abi-relocatable-arm.md"],
    );
}

#[test]
fn embedder_mpu_without_mpu_is_refused_1284() {
    assert_refused(
        &one_mem_fixture(),
        "flag_only",
        &[
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--embedder-mpu",
        ],
        &["--embedder-mpu acknowledges", "no effect"],
    );
}

/// With the acknowledgment the object is exactly what `none` produces — synth
/// adds no guard and no programming — and the manifest names who programs it.
#[test]
fn relocatable_mpu_with_the_acknowledgment_is_accepted_and_recorded_1284() {
    let f = one_mem_fixture();
    let common = ["--target", "cortex-m3", "--all-exports", "--relocatable"];
    let (mpu, mpu_path) = bytes(
        &f,
        "reloc_flag",
        &[&common[..], &["--safety-bounds", "mpu", "--embedder-mpu"]].concat(),
    );
    let (none, _) = bytes(
        &f,
        "reloc_none",
        &[&common[..], &["--safety-bounds", "none"]].concat(),
    );
    assert_eq!(mpu, none, "mpu + --embedder-mpu must be byte-identical to none");
    let manifest = std::fs::read_to_string(mpu_path.with_file_name(format!(
        "{}.safety-manifest.json",
        mpu_path.file_stem().unwrap().to_str().unwrap()
    )))
    .expect("safety manifest written next to the object");
    assert!(manifest.contains("\"safety_bounds\": \"mpu\""), "{manifest}");
    assert!(
        manifest.contains("\"mpu_programming\": \"embedder\""),
        "the manifest must record that the EMBEDDER programs the MPU: {manifest}"
    );
}

/// Multi-memory: accepted with the acknowledgment, and the object is the plain
/// relocatable object (memory k gets no guard under `mpu` — the embedder's
/// per-memory region is the enforcement).
#[test]
fn multi_memory_mpu_with_the_acknowledgment_matches_the_plain_object_1284() {
    let f = two_tenant_fixture();
    let common = [
        "--target",
        "cortex-m3",
        "--all-exports",
        "--relocatable",
        "--embedder-data-init",
    ];
    let (mpu, _) = bytes(
        &f,
        "two_flag",
        &[&common[..], &["--safety-bounds", "mpu", "--embedder-mpu"]].concat(),
    );
    let (plain, _) = bytes(&f, "two_plain", &common);
    assert_eq!(
        mpu, plain,
        "two-memory mpu + --embedder-mpu must equal the plain relocatable object"
    );
}
