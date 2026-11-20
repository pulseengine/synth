//! RQ-91-TARGETRECORD (Refs #1741): the `target-record` binary end to end,
//! and the boot contract the linked-image runner asserts.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;
use synth_oracle::emulate::Cpu;
use synth_oracle::image::BootedImage;
use synth_oracle::probes::PROBES_WAT;
use synth_oracle::record::validate_against_consumer_schema;
use synth_oracle::synth::{compile, synth_binary};

fn scratch(tag: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("target-record-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn generator() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_target-record"));
    if let Ok(s) = synth_binary() {
        cmd.env("SYNTH", s);
    }
    cmd
}

/// One cortex-m4 run with an EMPTY corpus directory, as an explicit partial
/// record. The written file must validate against the vendored consumer
/// schema; all four facts must be present (none omitted); the empty corpus
/// must read `ran: false` (never a passing row); the execution leg must pass
/// with its controls red on the Cortex-M4 model; hardware is never claimed.
#[test]
fn record_is_schema_valid_and_never_omits_a_fact() {
    let dir = scratch("e2e");
    let empty = dir.join("no-corpus");
    std::fs::create_dir_all(&empty).unwrap();
    let out = dir.join("north-star-input.O1.json");
    let o = generator()
        .args(["--targets", "cortex-m4", "--partial", "--spec-dir"])
        .arg(&empty)
        .arg("--work")
        .arg(dir.join("work"))
        .arg("--out")
        .arg(&out)
        .args(["--require-pass", "cortex-m4/execution_match"])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&o.stdout);
    eprintln!("{stdout}{}", String::from_utf8_lossy(&o.stderr));
    assert!(o.status.success(), "target-record failed: {:?}", o.status);

    let rec: Value = serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    validate_against_consumer_schema(&rec).unwrap();
    let facts = rec["facts"].as_array().unwrap();
    let get = |id: &str| -> &Value {
        facts
            .iter()
            .find(|f| f["id"] == id)
            .unwrap_or_else(|| panic!("fact {id} omitted"))
    };
    for field in ["reach", "execution_match", "wcet", "hardware_run"] {
        let f = get(&format!("cortex-m4/{field}"));
        assert_eq!(f["detail"]["target"], "cortex-m4");
        assert_eq!(f["detail"]["field"], field);
    }
    assert_eq!(facts.len(), 4);
    let r = get("cortex-m4/reach");
    assert_eq!(
        (r["ran"].as_bool(), r["pass"].as_bool()),
        (Some(false), Some(false)),
        "{r}"
    );
    assert!(r["detail"]["value"].is_null());
    let x = get("cortex-m4/execution_match");
    assert_eq!(x["pass"], true, "{x}");
    assert_eq!(x["control_failed_as_expected"], true);
    assert!(x["detail"]["executed_vectors"].as_u64().unwrap() >= 3024);
    assert_eq!(x["detail"]["value"]["wrong"], 0);
    assert!(
        x["detail"]["value"]["scope"]
            .as_str()
            .unwrap()
            .starts_with("probe set (21 probes, 3024 vectors)")
    );
    assert_eq!(x["detail"]["cpu_model_readback"], 9, "Cortex-M4 model id");
    let w = get("cortex-m4/wcet");
    assert_eq!(w["pass"], true, "{w}");
    assert_eq!(w["control_failed_as_expected"], true);
    let h = get("cortex-m4/hardware_run");
    assert_eq!(
        (h["ran"].as_bool(), h["pass"].as_bool()),
        (Some(false), Some(false))
    );
    assert!(stdout.contains("schema-valid, complete, 4 facts"));
}

/// A subset without `--partial`, and an output name that disagrees with the
/// objective, are refused before anything runs or is written.
#[test]
fn subset_and_misnamed_output_are_refused() {
    let dir = scratch("refuse");
    let out = dir.join("north-star-input.O1.json");
    let o = generator()
        .args(["--targets", "cortex-m4", "--out"])
        .arg(&out)
        .output()
        .unwrap();
    assert_eq!(o.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&o.stderr).contains("--partial"));
    assert!(!out.exists());
    let bad = dir.join("north-star-input.json");
    let o = generator().arg("--out").arg(&bad).output().unwrap();
    assert_eq!(o.status.code(), Some(2));
    assert!(!bad.exists());
}

/// REVIEW_17 finding 4: the boot is load-bearing. Three broken startups that
/// the earlier runner let through (3024 agree each) must now fail to boot,
/// and the unmodified image must boot.
#[test]
fn broken_startups_fail_the_boot_contract() {
    let dir = scratch("boot");
    let input = dir.join("probes.wasm");
    std::fs::write(&input, wat::parse_str(PROBES_WAT).unwrap()).unwrap();
    let out = dir.join("probes.elf");
    let run = compile(&input, &["--target", "cortex-m4", "--all-exports"], &out).unwrap();
    assert!(run.status.success(), "{}", run.stderr);
    let elf = std::fs::read(&out).unwrap();
    let img = BootedImage::boot_bytes(&elf, Cpu::CortexM4, false).expect("pristine image boots");
    assert_eq!(img.contract.r10_linear_memory_size, 0x1_0000);

    // Reset_Handler's bytes in the file: vector[1] & !1, first PT_LOAD.
    let u32_at = |b: &[u8], o: usize| u32::from_le_bytes(b[o..o + 4].try_into().unwrap()) as usize;
    let phoff = u32_at(&elf, 28);
    let text_off = u32_at(&elf, phoff + 4);
    let text_va = u32_at(&elf, phoff + 8);
    let r = text_off + (u32_at(&elf, text_off + 4) & !1) - text_va;

    let refused = |e: &[u8], what: &str| match BootedImage::boot_bytes(e, Cpu::CortexM4, false) {
        Ok(_) => panic!("{what}: booted"),
        Err(err) => {
            let s = format!("{err:?}");
            assert!(s.contains("boot contract broken"), "{what}: {s}");
        }
    };
    // (1) The R10/R11 initialisation (four movw/movt) replaced by NOPs.
    let mut e1 = elf.clone();
    for i in 0..8 {
        e1[r + 2 * i] = 0x00;
        e1[r + 2 * i + 1] = 0xBF;
    }
    refused(&e1, "R10/R11 init NOPed");
    // (2) R11 set to a wrong address: one bit of the movt immediate flipped.
    let mut e2 = elf.clone();
    e2[r + 12] ^= 0x04;
    refused(&e2, "R11 movt corrupted");
    // (3) The entry literal behind `blx r0` is garbage.
    let mut e3 = elf.clone();
    let lit = (0..40)
        .step_by(2)
        .find(|&o| e3[r + o] == 0x80 && e3[r + o + 1] == 0x47)
        .unwrap()
        + 6;
    e3[r + lit..r + lit + 4].copy_from_slice(&0xDEAD_BEEFu32.to_le_bytes());
    refused(&e3, "entry literal 0xDEADBEEF");
}
