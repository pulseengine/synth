//! #686 — `SYNTH_SHIFT_MASK_ELIDE`: elide the #682 mod-32 shift-amount mask
//! when the amount is statically provable < 32.
//!
//! Three gates, per the flag-then-flip protocol:
//!
//! 1. **Default is ON since v0.50.0 (#846)** — the flag flipped default-on to
//!    recover gale's gpio-thin +44 B regression (the pin bit-arithmetic emits
//!    `and rN,#0x1f` then the redundant #682 re-mask `and r12,#0x1f`). The
//!    flip re-froze the anchors (`frozen_codegen_bytes.rs`, all differentials
//!    re-run green on the new smaller bytes). This gate now pins unset ≡
//!    explicit `SYNTH_SHIFT_MASK_ELIDE=1` (the ON default) AND that the
//!    opt-out `SYNTH_SHIFT_MASK_ELIDE=0` STILL rolls back to the pre-flip
//!    bytes byte-for-byte — the escape hatch every flip lever owes.
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
//!
//! RQ-58-FLAKE (#977): this file was the one that kept reading a non-ELF. Its
//! output path was derived from `(fixture, relocatable, flag)` alone, and its
//! two `#[test]` fns walk the SAME corpus with the SAME flag values on parallel
//! libtest threads — so both wrote and read one `/tmp` file, and `synth
//! compile` truncates on open. Every compile now goes through
//! `artifact_guard`, which gives each call its own path and refuses to hand
//! back bytes it did not just watch the compiler produce. The guards are
//! observed firing by the `artifact_guard_*` tests at the bottom.

use std::collections::BTreeMap;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};

mod artifact_guard;

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
    "gpio_thin_846.loom.wasm",
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
    // #977: unique PER CALL, not per (fixture, flag) — the two #[test] fns below
    // request identical triples on parallel libtest threads, and a shared path
    // means one thread parses what the other is mid-way through truncating.
    let elf = artifact_guard::unique_artifact(
        &format!(
            "shift_mask_elide_686_{}_{}_{}",
            wasm.replace('.', "_"),
            relocatable,
            elide.unwrap_or("unset")
        ),
        "o",
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
        elf.to_str().unwrap(),
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--all-exports",
    ]);
    if relocatable {
        // RQ-59-DATASEG (#1041): the corpus carries data-segment fixtures;
        // this harness only reads codegen bytes/stats (bytes are identical
        // with the flag — it suppresses the new refusal only).
        cmd.args(["--relocatable", "--embedder-data-init"]);
    }
    let bytes = artifact_guard::compile_bytes_or_panic(
        &mut cmd,
        &elf,
        &format!("{wasm} (relocatable={relocatable}, elide={elide:?})"),
    );
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

/// Gate 1 (post-#846 flip): unset ≡ `SYNTH_SHIFT_MASK_ELIDE=1`, byte-for-byte
/// — the flag is DEFAULT-ON since v0.50.0. Also proves the opt-out escape
/// hatch: `SYNTH_SHIFT_MASK_ELIDE=0` must differ from the default on at least
/// one shift-heavy fixture (else the rollback lever is vacuous).
#[test]
fn shift_mask_elide_686_default_is_on_and_optout_rolls_back() {
    let mut optout_differs = false;
    for &(vname, reloc) in VARIANTS {
        for &wasm in CORPUS {
            let (unset, _) = compile(wasm, reloc, None);
            let (on, _) = compile(wasm, reloc, Some("1"));
            assert_eq!(
                unset, on,
                "{wasm} [{vname}]: default must equal explicit ON (flag is default-on since #846)"
            );
            let (off, _) = compile(wasm, reloc, Some("0"));
            if off != unset {
                optout_differs = true;
            }
        }
    }
    assert!(
        optout_differs,
        "SYNTH_SHIFT_MASK_ELIDE=0 never changed bytes — the opt-out rollback is vacuous"
    );
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

// ---------------------------------------------------------------------------
// RQ-58-FLAKE (#977) — the guard, observed firing.
//
// A guard nobody watched fire is not a guard, so the bad states are constructed
// deliberately here rather than described. These run in the same binary as the
// gates above, so CI re-observes them on every commit.
// ---------------------------------------------------------------------------

/// Build a command that is *guaranteed* to fail the compile without producing
/// an object: a nonexistent input. (`synth compile` exits 1 and writes nothing.)
fn failing_compile(out: &std::path::Path) -> Command {
    let mut cmd = Command::new(synth());
    cmd.args([
        "compile",
        "/nonexistent/rq58-flake-977-there-is-no-such-module.wat",
        "-o",
        out.to_str().unwrap(),
        "-b",
        "arm",
        "--target",
        "cortex-m4",
    ]);
    cmd
}

/// A command that compiles a real fixture successfully — used to mint a genuine
/// ELF to pre-plant as "the previous run's object".
fn good_compile(out: &std::path::Path) -> Command {
    let mut cmd = Command::new(synth());
    cmd.env_remove("SYNTH_SHIFT_MASK_ELIDE");
    cmd.args([
        "compile",
        fixture("i32_shift_mask_682.wat").to_str().unwrap(),
        "-o",
        out.to_str().unwrap(),
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--all-exports",
        "--relocatable",
        "--embedder-data-init",
    ]);
    cmd
}

/// LOUD direction. A bad compile must report as a bad compile — at the compile,
/// with the compiler's own stderr — and never as `Could not read file magic`
/// twenty lines later in a parser.
#[test]
fn artifact_guard_reports_a_failed_compile_as_a_failed_compile() {
    let out = artifact_guard::unique_artifact("guard_failed_compile", "o");
    let err = artifact_guard::compile_artifact(&mut failing_compile(&out), &out)
        .expect_err("a compile of a nonexistent module must not yield bytes");

    assert!(
        err.contains("synth compile FAILED"),
        "the failure must name the compile as the failure, got: {err}"
    );
    assert!(
        err.contains("Failed to read input file"),
        "the compiler's OWN stderr must travel with the failure, got: {err}"
    );
    assert!(
        !err.contains("file magic"),
        "the parser must never be the one to complain, got: {err}"
    );
}

/// SILENT direction — the one that matters.
///
/// Pre-plant a genuine, parseable ELF at the output path (the previous run's
/// object), then fail the compile. The pre-#977 shape — `fs::read` the path and
/// `File::parse` it — would have parsed those stale bytes and PASSED the gate on
/// evidence this invocation never produced. That is the v0.56 trap with the sign
/// flipped, and it is a false green rather than a noisy red.
///
/// The guard must REFUSE, and must leave nothing at the path for anyone to pick
/// up afterwards.
#[test]
fn artifact_guard_refuses_a_stale_artifact_instead_of_passing_on_it() {
    // A real, whole ELF — produced by a compile we know succeeded.
    let src = artifact_guard::unique_artifact("guard_stale_source", "o");
    let good_bytes = artifact_guard::compile_artifact_or_panic(
        &mut good_compile(&src),
        &src,
        "minting the stale artifact",
    );
    let _ = std::fs::remove_file(&src);
    let stale = artifact_guard::unique_artifact("guard_stale_planted", "o");
    std::fs::write(&stale, &good_bytes).expect("plant the stale artifact");

    // Establish the counterfactual: these bytes ARE a valid ELF with a .text,
    // i.e. an unguarded compile-then-parse would have sailed straight through.
    let planted = std::fs::read(&stale).expect("read planted");
    let obj = object::File::parse(&*planted).expect("the planted artifact is a valid ELF");
    assert!(
        obj.section_by_name(".text").is_some(),
        "the planted artifact must be substantial enough to fool an unguarded gate"
    );

    // Now the compile fails while that stale object is sitting at the path.
    let err = artifact_guard::compile_artifact(&mut failing_compile(&stale), &stale)
        .expect_err("REFUSAL REQUIRED: a failed compile must not return last run's bytes");
    assert!(
        err.contains("synth compile FAILED"),
        "the refusal must name the compile failure, got: {err}"
    );
    assert!(
        !err.contains("file magic"),
        "and must not surface as a parse error, got: {err}"
    );
    assert!(
        !std::path::Path::new(&stale).exists(),
        "the stale artifact must have been removed BEFORE the compile ran — \
         leaving it there is how a later reader picks up the wrong object"
    );
}

/// The empty-file case, shown against the exact historical symptom: the same
/// zero bytes that make `object` say `Could not read file magic` are reported by
/// the guard as an empty artifact, before any parser sees them.
#[test]
fn artifact_guard_reports_an_empty_artifact_precisely() {
    let out = artifact_guard::unique_artifact("guard_empty", "o");
    std::fs::write(&out, b"").expect("create empty");

    // This is verbatim what #960/#974/#977 reported, from the unguarded shape.
    let unguarded = object::File::parse(&*std::fs::read(&out).unwrap())
        .expect_err("empty bytes are not an ELF");
    assert!(
        format!("{unguarded}").contains("Could not read file magic"),
        "sanity: the historical symptom is the empty-file parse, got: {unguarded}"
    );

    let err = artifact_guard::read_artifact(&out).expect_err("an empty artifact must be refused");
    assert!(
        err.contains("EMPTY"),
        "the guard must name emptiness, got: {err}"
    );
    let _ = std::fs::remove_file(&out);
}

/// And the missing-file case: no artifact means no parse, with the path named.
#[test]
fn artifact_guard_reports_a_missing_artifact_precisely() {
    let out = artifact_guard::unique_artifact("guard_missing", "o");
    let err = artifact_guard::read_artifact(&out).expect_err("a missing artifact must be refused");
    assert!(
        err.contains("was NOT created by this invocation"),
        "the guard must say the artifact is absent, got: {err}"
    );
}

/// The collision itself: two calls that describe the SAME compile must still get
/// different paths. This is what makes the two `#[test]` fns above unable to
/// race, on any runner, however the scheduler interleaves them.
#[test]
fn artifact_guard_paths_are_unique_per_call() {
    let a = artifact_guard::unique_artifact("shift_mask_elide_686_same_tag", "o");
    let b = artifact_guard::unique_artifact("shift_mask_elide_686_same_tag", "o");
    assert_ne!(
        a, b,
        "identical descriptions must NOT map to one path — that is #977"
    );
}
