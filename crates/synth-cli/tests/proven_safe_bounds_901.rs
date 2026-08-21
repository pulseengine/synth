//! VCR-MEM-004 / #901 — end-to-end byte gates for `--proven-safe`.
//!
//! The three safety properties the lane exists to establish, each locked on
//! the REAL compiled bytes of `scripts/repro/proven_safe_bounds_901.wat` (one
//! function, 8 `--safety-bounds software` guarded accesses: 5 off a provably
//! bounded base, 3 off an unconstrained i32 param):
//!
//! 1. **FAIL CLOSED on `module_sha256` mismatch** — a stale verdict file
//!    elides NOTHING and the `.text` is BYTE-IDENTICAL to the guarded
//!    baseline. Also covered: a wrong `memory_min_bytes`, a wrong schema, a
//!    malformed file and a missing file. Every one warns and exits 0.
//! 2. **ABSENCE MEANS "NOT PROVEN", NEVER "UNSAFE"** — a list covering 5 of
//!    the 8 sites leaves EXACTLY 3 guards standing (80 B = 5 x 16 B saved),
//!    and the 3 survivors are precisely the `$raw`-addressed ones. Proven by
//!    a partial list, not by an empty one.
//! 3. **A GENUINE ELISION** — the full 8-site list strips every guard and
//!    lands byte-identical to the `--safety-bounds`-off floor: under the
//!    proof, the sandbox tax is exactly zero.
//!
//! Plus the key-space canary (byte offsets instead of operator indices elide
//! nothing LOUDLY), the loud zero-elision diagnostics, and the sigil
//! attestation on BOTH the accepted and the refused path.
//!
//! Execution evidence (elided ≡ checked ≡ wasmtime in-bounds; a NOT-proven
//! out-of-bounds access still TRAPS) lives in
//! `scripts/repro/proven_safe_bounds_901_differential.py`. Frozen anchors are
//! untouched by construction — the mark vector defaults empty.

use object::{Object, ObjectSection, ObjectSymbol};
use std::path::PathBuf;
use std::process::Command;
use synth_core::proven_safe::hex_sha256;

// #977 RQ-59-FRESHNESS: nothing here parses an artifact until the artifact is
// proven to be THIS invocation's output — see `artifact_guard`. The elision
// ATTESTATION sidecar derives its path from the elf path, so a unique elf
// path makes the sidecar fresh-by-construction too.
mod artifact_guard;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// The fixture's PROVEN access sites: `(pc, op, width)`. Pinned here and in
/// the `.wat` comments; the ingestion re-validates each against the decoded
/// operator, so a decoder drift fails loudly rather than eliding a wrong site.
const PROVEN: &[(u32, &str, u32)] = &[
    (9, "i32.load8_u", 1),
    (11, "i32.load8_u", 1),
    (14, "i32.load16_u", 2),
    (17, "i32.load", 4),
    (22, "i32.store8", 1),
];

/// The fixture's NOT-PROVEN sites — `$raw` is an unconstrained parameter.
const NOT_PROVEN: &[(u32, &str, u32)] = &[
    (24, "i32.load", 4),
    (29, "i32.load8_u", 1),
    (35, "i32.store", 4),
];

/// MEASURED guard cost on this fixture (cortex-m4, symtab slices). The #752
/// wraparound-safe guard is NOT a uniform size — the address form differs per
/// site — so these are the measured partition costs, not a per-site formula:
///
///   floor (no --safety-bounds)         probe =  94 B, 0 UDF#0
///   guarded (all 8 sites)              probe = 232 B, 16 UDF#0  => tax 138 B
///   5 proven elided                    probe = 152 B, 6 UDF#0   => saved  80 B
///   3 unproven elided (mirror image)   probe = 182 B, 10 UDF#0  => saved  50 B
///
/// 80 + 50 = 130 < 138: eliding EVERY guard additionally collapses 8 B of
/// address materialization that survives while any guard remains. Recorded
/// because it is the honest number, not the flattering one.
const TAX_ALL_8: usize = 138;
const SAVED_PROVEN_5: usize = 80;
const SAVED_UNPROVEN_3: usize = 50;

const UDF0: u16 = 0xDE00;

fn dir() -> PathBuf {
    let d = std::env::temp_dir().join("proven_safe_bounds_901");
    std::fs::create_dir_all(&d).expect("mk tempdir");
    d
}

fn fixture_wasm() -> Vec<u8> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/proven_safe_bounds_901.wat");
    let wat = std::fs::read(path).expect("read fixture wat");
    wat::parse_bytes(&wat)
        .expect("fixture wat must parse")
        .into_owned()
}

/// Build a `scry/safe-accesses/v1` document over `sites`.
fn safe_accesses(hash: &str, min_bytes: u64, sites: &[(u32, &str, u32)]) -> String {
    let entries: Vec<String> = sites
        .iter()
        .map(|(pc, op, w)| format!(r#"{{"func":0,"pc":{pc},"op":"{op}","width":{w}}}"#))
        .collect();
    format!(
        r#"{{ "schema": "scry/safe-accesses/v1", "scry_version": "3.2.4",
              "module_sha256": "{hash}", "memory_min_bytes": {min_bytes},
              "premises": {{ "bounded_memory": true }},
              "counts": {{ "access_sites": 8, "proven_safe": {} }},
              "proven_safe": [{}] }}"#,
        sites.len(),
        entries.join(",\n")
    )
}

struct Compiled {
    text: Vec<u8>,
    probe: Vec<u8>,
    stderr: String,
    stdout: String,
    attestation: Option<serde_json::Value>,
}

impl Compiled {
    fn udf_count(&self) -> usize {
        self.probe
            .as_chunks::<2>()
            .0
            .iter()
            .filter(|&&c| u16::from_le_bytes(c) == UDF0)
            .count()
    }
}

/// Compile the fixture. `verdicts` is the `safe-accesses.json` body (written
/// next to the module), `Some(None)` means "point --proven-safe at a file that
/// does not exist".
fn compile(tag: &str, software_bounds: bool, verdicts: Option<Option<&str>>) -> Compiled {
    let d = dir();
    let input = d.join(format!("{tag}.wasm"));
    // #977: unique per call + remove-first + status/exists/non-empty guards;
    // the attestation sidecar path derives from the elf path, so it is fresh
    // by construction as well.
    let elf = artifact_guard::unique_artifact(&format!("psb901_{tag}"), "elf");
    std::fs::write(&input, fixture_wasm()).expect("write wasm");

    let mut cmd = Command::new(synth());
    cmd.args([
        "compile",
        input.to_str().unwrap(),
        "-o",
        elf.to_str().unwrap(),
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--all-exports",
    ]);
    if software_bounds {
        cmd.args(["--safety-bounds", "software"]);
    }
    if let Some(body) = verdicts {
        let json = d.join(format!("{tag}.safe-accesses.json"));
        match body {
            Some(b) => std::fs::write(&json, b).expect("write verdicts"),
            None => {
                let _ = std::fs::remove_file(&json);
            }
        }
        cmd.args(["--proven-safe", json.to_str().unwrap()]);
    }
    // Never let an ambient fact-spec lever perturb these gates.
    cmd.env_remove("SYNTH_FACT_SPEC");
    cmd.env_remove("SYNTH_FACT_SPEC_FORCE_ADMIT");

    let (bytes, out) =
        artifact_guard::compile_artifact_with_output(&mut cmd, &elf).unwrap_or_else(|e| {
            panic!(
                "compile '{tag}' FAILED (a verdict file must never turn a good \
                 compile into a failed one): {e}"
            )
        });
    let obj = object::File::parse(&*bytes).expect("parse elf");
    let sec = obj.section_by_name(".text").expect(".text");
    let text = sec.data().expect("read .text").to_vec();
    let base = sec.address();
    let end = base + text.len() as u64;
    // Symtab slices, never disasm text (the #489 lesson).
    let mut syms: Vec<(String, u64)> = obj
        .symbols()
        .filter(|s| {
            let a = s.address() & !1;
            !s.name().unwrap_or("").is_empty() && a >= base && a < end
        })
        .map(|s| (s.name().unwrap().to_string(), (s.address() & !1) - base))
        .collect();
    syms.sort_by_key(|&(_, a)| a);
    let mut probe = Vec::new();
    for (i, (name, start)) in syms.iter().enumerate() {
        if name == "probe" {
            let stop = syms
                .get(i + 1)
                .map(|&(_, a)| a as usize)
                .unwrap_or(text.len())
                .min(text.len());
            probe = text[*start as usize..stop].to_vec();
        }
    }
    assert!(!probe.is_empty(), "symbol 'probe' missing from symtab");

    let att_path = synth_core::proven_safe::ElisionAttestation::sidecar_path(&elf);
    let attestation = std::fs::read_to_string(&att_path)
        .ok()
        .map(|s| serde_json::from_str(&s).expect("attestation is valid JSON"));
    // Per-call unique names would otherwise accumulate on a long-lived runner.
    let _ = std::fs::remove_file(&elf);
    let _ = std::fs::remove_file(&att_path);

    Compiled {
        text,
        probe,
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        attestation,
    }
}

fn module_hash() -> String {
    hex_sha256(&fixture_wasm())
}

fn all_sites() -> Vec<(u32, &'static str, u32)> {
    let mut v = PROVEN.to_vec();
    v.extend_from_slice(NOT_PROVEN);
    v
}

// =============================================================================
// PROPERTY 3 — a genuine elision
// =============================================================================

/// The full 8-site proof strips every guard: the `.text` lands BYTE-IDENTICAL
/// to the `--safety-bounds`-off floor. Under the proof the sandbox bounds tax
/// is exactly zero, which is the capability claim.
#[test]
fn full_proof_reaches_the_unguarded_floor_901() {
    let floor = compile("floor", false, None);
    let guarded = compile("guarded", true, None);
    let doc = safe_accesses(&module_hash(), 65536, &all_sites());
    let elided = compile("all8", true, Some(Some(&doc)));

    assert_eq!(guarded.udf_count(), 16, "8 guards x 2 UDF#0 each");
    assert_eq!(elided.udf_count(), 0, "every guard must be gone");
    assert_eq!(
        elided.probe, floor.probe,
        "a fully proven function must lower EXACTLY like the unguarded floor"
    );
    assert_eq!(
        guarded.probe.len() - elided.probe.len(),
        TAX_ALL_8,
        "the whole 8-site guard tax must go"
    );
    assert!(
        elided.stderr.contains("proven-safe: ACCEPTED"),
        "{}",
        elided.stderr
    );
}

// =============================================================================
// PROPERTY 2 — absence means "not proven", NEVER "unsafe"
// =============================================================================

/// A PARTIAL list (5 of 8) must leave EXACTLY 3 guards standing — and the 3
/// survivors must be the `$raw`-addressed accesses, not an arbitrary 3. Proven
/// against the partial list, not the vacuous empty one.
#[test]
fn partial_proof_leaves_exactly_the_unproven_guards_901() {
    let guarded = compile("part_base", true, None);
    let doc = safe_accesses(&module_hash(), 65536, PROVEN);
    let part = compile("part", true, Some(Some(&doc)));

    assert_eq!(
        part.udf_count(),
        6,
        "3 unproven sites x 2 UDF#0 must survive; got {} — stderr: {}",
        part.udf_count(),
        part.stderr
    );
    assert_eq!(
        guarded.probe.len() - part.probe.len(),
        SAVED_PROVEN_5,
        "exactly the 5 proven sites' guards may vanish"
    );
    // ...and the survivors are structurally the same lowering as a build that
    // proves ONLY the three unproven sites' complement: compile the mirror
    // image and confirm the two partitions are disjoint and complete.
    let mirror_doc = safe_accesses(&module_hash(), 65536, NOT_PROVEN);
    let mirror = compile("part_mirror", true, Some(Some(&mirror_doc)));
    assert_eq!(
        mirror.udf_count(),
        10,
        "5 proven sites' guards must survive"
    );
    assert_eq!(
        guarded.probe.len() - mirror.probe.len(),
        SAVED_UNPROVEN_3,
        "exactly the 3 unproven sites' guards may vanish in the mirror build"
    );
    // The two partitions are disjoint and cover all 8 guards (16 UDF pairs)...
    assert_eq!(part.udf_count() + mirror.udf_count(), 16);
    // ...though their byte savings sum to LESS than the whole tax: 8 B of
    // address materialization only collapses once NO guard remains.
    assert_eq!(SAVED_PROVEN_5 + SAVED_UNPROVEN_3 + 8, TAX_ALL_8);
    assert!(
        part.stderr.contains("op indices [9, 11, 14, 17, 22]"),
        "{}",
        part.stderr
    );
}

/// An accepted document that proves NOTHING elides nothing — and says so.
#[test]
fn vacuous_document_elides_nothing_loudly_901() {
    let guarded = compile("vac_base", true, None);
    let doc = safe_accesses(&module_hash(), 65536, &[]);
    let vac = compile("vac", true, Some(Some(&doc)));
    assert_eq!(vac.probe, guarded.probe);
    assert!(
        vac.stderr.contains("ZERO access sites") && vac.stderr.contains("NOTHING was elided"),
        "an accepted-but-vacuous document must be loud: {}",
        vac.stderr
    );
}

// =============================================================================
// PROPERTY 1 — FAIL CLOSED
// =============================================================================

/// THE headline refusal: a `module_sha256` that does not name this module
/// elides NOTHING. Byte-identical to the guarded baseline, warns loudly,
/// exits 0.
#[test]
fn stale_hash_elides_nothing_and_is_byte_identical_901() {
    let guarded = compile("stale_base", true, None);
    // One nibble off — the shape a re-built or rewritten module produces.
    let mut h = module_hash();
    let last = h.pop().unwrap();
    h.push(if last == 'a' { 'b' } else { 'a' });
    let doc = safe_accesses(&h, 65536, &all_sites());
    let stale = compile("stale", true, Some(Some(&doc)));

    assert_eq!(
        stale.text, guarded.text,
        "a stale analysis must not move a single byte"
    );
    assert_eq!(stale.udf_count(), 16, "every guard must survive");
    assert!(
        stale.stderr.contains("REFUSED — module_sha256 mismatch"),
        "{}",
        stale.stderr
    );
    assert!(
        stale.stderr.contains("memory-safety hole"),
        "the refusal must say WHY, not just that: {}",
        stale.stderr
    );
    // Both hashes are named so an operator can tell which module it was for.
    assert!(stale.stderr.contains(&h) && stale.stderr.contains(&module_hash()));
}

/// The verdicts are proven against scry's declared floor. If it disagrees with
/// synth's declared minimum, the producer is broken — refuse.
#[test]
fn memory_min_bytes_disagreement_elides_nothing_901() {
    let guarded = compile("floor_base", true, None);
    let doc = safe_accesses(&module_hash(), 131072, &all_sites());
    let bad = compile("floorbad", true, Some(Some(&doc)));
    assert_eq!(bad.text, guarded.text);
    assert!(
        bad.stderr.contains("memory_min_bytes disagreement"),
        "{}",
        bad.stderr
    );
}

/// Malformed, missing and wrong-schema documents: no elisions, a diagnostic,
/// exit 0 — never an error, never partial trust. The `wsc.facts` fail-safe
/// skew rule.
#[test]
fn malformed_missing_and_wrong_schema_elide_nothing_without_failing_901() {
    let guarded = compile("bad_base", true, None);
    let h = module_hash();
    let cases: Vec<(&str, Option<String>)> = vec![
        ("missing", None),
        ("garbage", Some("not json at all {{{".to_string())),
        ("empty", Some(String::new())),
        (
            "wrongschema",
            Some(safe_accesses(&h, 65536, PROVEN).replace("safe-accesses/v1", "safe-accesses/v2")),
        ),
        (
            "nohash",
            Some(r#"{"schema":"scry/safe-accesses/v1","memory_min_bytes":65536}"#.to_string()),
        ),
        (
            "sitegarbage",
            Some(safe_accesses(&h, 65536, PROVEN).replace(r#""pc":9"#, r#""pc":"nine""#)),
        ),
    ];
    for (tag, body) in cases {
        let c = compile(tag, true, Some(body.as_deref()));
        assert_eq!(
            c.text, guarded.text,
            "'{tag}' moved bytes; stderr: {}",
            c.stderr
        );
        assert!(
            c.stderr.contains("proven-safe"),
            "'{tag}' refused SILENTLY: {}",
            c.stderr
        );
        // Attested as refused, so sigil sees the refusal too.
        let att = c.attestation.expect("attestation is written on refusal");
        assert_eq!(att["accepted"], serde_json::json!(false), "'{tag}'");
        assert!(
            att["refusal"].is_string(),
            "'{tag}' refused without a reason"
        );
    }
}

/// THE KEY-SPACE CANARY. scry#114's `pc` is the 0-based OPERATOR index; if a
/// producer ever emitted wasm BYTE OFFSETS instead, the entries must fail
/// validation and the build must elide NOTHING loudly — never strip a guard
/// off the wrong access.
#[test]
fn byte_offsets_instead_of_operator_indices_elide_nothing_loudly_901() {
    let guarded = compile("keys_base", true, None);
    // Plausible byte offsets for this body — all far past the 38-operator count.
    let bogus: Vec<(u32, &str, u32)> = vec![
        (41, "i32.load8_u", 1),
        (45, "i32.load8_u", 1),
        (52, "i32.load16_u", 2),
        (61, "i32.load", 4),
        (77, "i32.store8", 1),
    ];
    let doc = safe_accesses(&module_hash(), 65536, &bogus);
    let c = compile("keys", true, Some(Some(&doc)));

    assert_eq!(c.text, guarded.text, "a wrong key space must move NO bytes");
    assert_eq!(c.udf_count(), 16);
    assert!(c.stderr.contains("proven-safe: DROP"), "{}", c.stderr);
    assert!(
        c.stderr.contains("out of range") && c.stderr.contains("OPERATOR index"),
        "the drop must name the likely cause: {}",
        c.stderr
    );
    assert!(
        c.stderr.contains("NOTHING was elided"),
        "accepted-but-zero-elisions must be loud: {}",
        c.stderr
    );
    let att = c.attestation.expect("attestation written");
    assert_eq!(att["accepted"], serde_json::json!(true));
    assert_eq!(att["sites_offered"], serde_json::json!(5));
    assert_eq!(att["sites_elided"], serde_json::json!(0));
    assert_eq!(att["sites_not_elided"], serde_json::json!(5));
}

/// A width that disagrees with the decoded operator changes which BYTES are
/// covered — drop that entry, keep the sound ones.
#[test]
fn width_skew_drops_only_the_skewed_site_901() {
    let guarded = compile("w_base", true, None);
    let mut sites = PROVEN.to_vec();
    sites[0] = (9, "i32.load", 4); // pc 9 is really a 1 B load8_u
    let doc = safe_accesses(&module_hash(), 65536, &sites);
    let c = compile("w", true, Some(Some(&doc)));
    assert_eq!(
        c.udf_count(),
        8,
        "4 sound sites elide, the width-skewed one keeps its guard (4 guards x 2 UDF)"
    );
    assert!(
        c.probe.len() > guarded.probe.len() - SAVED_PROVEN_5,
        "the skewed site's guard must still cost bytes"
    );
    assert!(
        c.stderr.contains("disagrees with the decoded operator"),
        "{}",
        c.stderr
    );
}

/// `--proven-safe` under a bounds mode that emits no inline guard: there is
/// nothing to strip, and that is stated rather than reported as success.
#[test]
fn no_software_bounds_means_nothing_to_elide_and_says_so_901() {
    let floor = compile("nb_base", false, None);
    let doc = safe_accesses(&module_hash(), 65536, &all_sites());
    let c = compile("nb", false, Some(Some(&doc)));
    assert_eq!(c.probe, floor.probe);
    assert!(
        c.stderr.contains("not `software`") && c.stderr.contains("NOTHING was elided"),
        "{}",
        c.stderr
    );
}

/// Without the flag nothing changes at all — the default path is untouched.
#[test]
fn flag_absent_writes_no_attestation_and_no_marks_901() {
    let a = compile("noflag_a", true, None);
    let b = compile("noflag_b", true, None);
    assert_eq!(a.text, b.text);
    assert!(a.attestation.is_none(), "no flag ⇒ no sidecar");
    assert!(!a.stderr.contains("proven-safe"));
}

// =============================================================================
// Never silently do nothing — the #865 shape
// =============================================================================

/// Only the ARM direct selector consumes the marks. RISC-V and aarch64 accept
/// `--safety-bounds software` but emit their own guards from their own
/// selectors, so nothing is stripped there. The attestation must record ZERO
/// elisions and NAME the backend — a sidecar claiming elisions the backend
/// never performed is worse than no sidecar at all.
///
/// (This is exactly what shipped before the gate: `-b riscv` and
/// `-b aarch64` both wrote `sites_elided: 5` while the ELF was byte-identical
/// to the guarded baseline.)
#[test]
fn non_arm_backends_attest_zero_elisions_901() {
    let d = dir();
    let input = d.join("xback.wasm");
    std::fs::write(&input, fixture_wasm()).expect("write wasm");
    let json = d.join("xback.safe-accesses.json");
    std::fs::write(&json, safe_accesses(&module_hash(), 65536, PROVEN)).expect("write");

    for (backend, target) in [("riscv", "rv32imac"), ("aarch64", "cortex-a53")] {
        let run = |with_verdicts: bool, tag: &str| -> (Vec<u8>, String, PathBuf) {
            // #977: unique per call; the sidecar derives from the elf path.
            let elf =
                artifact_guard::unique_artifact(&format!("psb901_xback_{backend}_{tag}"), "elf");
            let mut cmd = Command::new(synth());
            cmd.args([
                "compile",
                input.to_str().unwrap(),
                "-o",
                elf.to_str().unwrap(),
                "-b",
                backend,
                "--target",
                target,
                "--all-exports",
                "--safety-bounds",
                "software",
            ]);
            if with_verdicts {
                cmd.args(["--proven-safe", json.to_str().unwrap()]);
            }
            let (bytes, out) = artifact_guard::compile_artifact_with_output(&mut cmd, &elf)
                .unwrap_or_else(|e| panic!("{backend} compile failed: {e}"));
            (
                bytes,
                String::from_utf8_lossy(&out.stderr).into_owned(),
                elf,
            )
        };
        let (base, _, _) = run(false, "base");
        let (with, stderr, with_elf) = run(true, "with");

        assert_eq!(
            base, with,
            "{backend}: --proven-safe must not move a byte on a backend that does \
             not consume the marks"
        );
        assert!(
            stderr.contains(&format!("`{backend}` backend does not consume")),
            "{backend}: the zero-elision reason must name the backend: {stderr}"
        );
        let att: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(synth_core::proven_safe::ElisionAttestation::sidecar_path(
                &with_elf,
            ))
            .expect("attestation written"),
        )
        .expect("valid JSON");
        assert_eq!(
            att["sites_elided"],
            serde_json::json!(0),
            "{backend}: the attestation must NOT claim elisions the backend never made"
        );
        assert_eq!(att["sites_offered"], serde_json::json!(5), "{backend}");
    }
}

/// The single-function path (`--func-index` / `--func-name`) builds no marks
/// and writes no attestation, so accepting `--proven-safe` there would be a
/// SILENT NO-OP on a safety-relevant flag — the #865 defect. Refuse loudly.
#[test]
fn single_function_path_refuses_the_flag_rather_than_ignoring_it_901() {
    let d = dir();
    let input = d.join("singlefn.wasm");
    std::fs::write(&input, fixture_wasm()).expect("write wasm");
    let json = d.join("singlefn.safe-accesses.json");
    std::fs::write(&json, safe_accesses(&module_hash(), 65536, PROVEN)).expect("write");
    let elf = d.join("singlefn.elf");

    let out = Command::new(synth())
        .args([
            "compile",
            input.to_str().unwrap(),
            "-o",
            elf.to_str().unwrap(),
            "-b",
            "arm",
            "--target",
            "cortex-m4",
            "--func-index",
            "0",
            "--safety-bounds",
            "software",
            "--proven-safe",
            json.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");

    assert!(
        !out.status.success(),
        "a flag that cannot be honoured must FAIL, not silently do nothing"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("not consumed on the single-function path"),
        "{stderr}"
    );
    // ...and it names the invocation that DOES work.
    assert!(stderr.contains("--all-exports"), "{stderr}");
}

// =============================================================================
// Attestation — what sigil reads
// =============================================================================

#[test]
fn attestation_records_the_elision_set_and_its_authority_901() {
    let doc = safe_accesses(&module_hash(), 65536, PROVEN);
    let c = compile("att", true, Some(Some(&doc)));
    let att = c.attestation.expect("attestation written");

    assert_eq!(
        att["schema"],
        serde_json::json!("synth-proven-safe-elisions-v1")
    );
    assert_eq!(att["accepted"], serde_json::json!(true));
    assert_eq!(att["scry_version"], serde_json::json!("3.2.4"));
    assert_eq!(att["module_sha256"], serde_json::json!(module_hash()));
    assert_eq!(
        att["declared_module_sha256"],
        serde_json::json!(module_hash())
    );
    assert_eq!(att["memory_min_bytes"], serde_json::json!(65536));
    assert_eq!(att["safety_bounds"], serde_json::json!("software"));
    assert_eq!(
        att["synth_version"],
        serde_json::json!(env!("CARGO_PKG_VERSION"))
    );
    assert_eq!(att["sites_offered"], serde_json::json!(5));
    assert_eq!(att["sites_elided"], serde_json::json!(5));
    assert_eq!(att["sites_not_elided"], serde_json::json!(0));

    let elisions = att["elisions"].as_array().expect("elisions array");
    assert_eq!(elisions.len(), PROVEN.len());
    for (e, (pc, op, w)) in elisions.iter().zip(PROVEN) {
        assert_eq!(e["func"], serde_json::json!(0));
        assert_eq!(e["pc"], serde_json::json!(pc));
        assert_eq!(e["op"], serde_json::json!(op));
        assert_eq!(e["width"], serde_json::json!(w));
        // On whose authority — the field that keeps a scry elision
        // distinguishable from a #494 ordeal-certificate one.
        assert_eq!(e["authority"], serde_json::json!("scry/safe-accesses/v1"));
    }
    assert!(c.stdout.contains("Proven-safe: wrote"), "{}", c.stdout);
}

/// SYNTH_FACT_SPEC may REWRITE the op stream, renumbering the index space the
/// verdicts are keyed in. The combination is REFUSED per function, never
/// silently remapped. Needs the solver-carrying build (the pass is a no-op
/// without it), so this runs under `--features verify`.
#[cfg(feature = "verify")]
#[test]
fn fact_spec_specialization_refuses_the_scry_marks_901() {
    // A `wsc.facts` value-range premise on the first `local.get $slot` gives
    // the fact-spec pass something to specialize, which is all this needs.
    fn leb_u32(mut v: u32, out: &mut Vec<u8>) {
        loop {
            let mut b = (v & 0x7f) as u8;
            v >>= 7;
            if v != 0 {
                b |= 0x80;
            }
            out.push(b);
            if v == 0 {
                return;
            }
        }
    }
    fn leb_s64(mut v: i64, out: &mut Vec<u8>) {
        loop {
            let mut b = (v & 0x7f) as u8;
            v >>= 7;
            let done = (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0);
            if !done {
                b |= 0x80;
            }
            out.push(b);
            if done {
                return;
            }
        }
    }
    let mut wasm = fixture_wasm();
    let mut body = Vec::new();
    leb_s64(0, &mut body);
    leb_s64(63, &mut body);
    let mut payload = vec![0x01u8];
    leb_u32(1, &mut payload);
    payload.push(0x01);
    leb_u32(0, &mut payload);
    leb_u32(0, &mut payload);
    leb_u32(body.len() as u32, &mut payload);
    payload.extend_from_slice(&body);
    let name = b"wsc.facts";
    let mut content = Vec::new();
    leb_u32(name.len() as u32, &mut content);
    content.extend_from_slice(name);
    content.extend_from_slice(&payload);
    wasm.push(0x00);
    leb_u32(content.len() as u32, &mut wasm);
    wasm.extend_from_slice(&content);

    let d = dir();
    let input = d.join("factspec.wasm");
    // #977: unique per call; the sidecar derives from the elf path.
    let elf = artifact_guard::unique_artifact("psb901_factspec", "elf");
    let json = d.join("factspec.safe-accesses.json");
    std::fs::write(&input, &wasm).expect("write wasm");
    std::fs::write(&json, safe_accesses(&hex_sha256(&wasm), 65536, PROVEN)).expect("write");

    let mut cmd = Command::new(synth());
    cmd.args([
        "compile",
        input.to_str().unwrap(),
        "-o",
        elf.to_str().unwrap(),
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--all-exports",
        "--safety-bounds",
        "software",
        "--proven-safe",
        json.to_str().unwrap(),
    ])
    .env("SYNTH_FACT_SPEC", "1")
    .env_remove("SYNTH_FACT_SPEC_FORCE_ADMIT");
    let (_elf_bytes, out) = artifact_guard::compile_artifact_with_output(&mut cmd, &elf)
        .unwrap_or_else(|e| panic!("factspec compile failed: {e}"));
    let stderr = String::from_utf8_lossy(&out.stderr);
    // NON-VACUITY FIRST: the pass must actually specialize this function,
    // otherwise the refusal below is never exercised and this test asserts
    // nothing. It admits the redundant-mask elision on `slot & 63` under the
    // premise, which DELETES two operators (38 -> 36) and renumbers every
    // index after them — exactly the skew the refusal exists for.
    assert!(
        stderr.contains("'probe' specialized"),
        "the fact-spec pass must specialize this fixture or this gate is \
         vacuous — the refusal path would never run: {stderr}"
    );
    assert!(
        stderr.contains("38 → 36 ops"),
        "the specialization must RENUMBER the operator index space (that is \
         what makes the scry keys stale): {stderr}"
    );
    assert!(
        stderr.contains("REFUSED: SYNTH_FACT_SPEC specialized this function"),
        "a renumbered op stream must refuse the scry marks: {stderr}"
    );
    // And the refusal must be total: nothing elided, attested as such.
    let att: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(synth_core::proven_safe::ElisionAttestation::sidecar_path(
            &elf,
        ))
        .expect("attestation written"),
    )
    .expect("valid JSON");
    assert_eq!(att["sites_elided"], serde_json::json!(0));
    assert_eq!(att["sites_offered"], serde_json::json!(5));
}
