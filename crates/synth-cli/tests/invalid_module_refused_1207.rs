//! #1207 — a module that does not VALIDATE is refused, on every backend and
//! every entry path, and no object is written.
//!
//! Before the fix nothing validated the input. The issue's module
//!
//! ```wat
//! (func (export "cu_add_tee") (param i32) (result i32) (local i32)
//!   (loop (result i32)
//!     local.get 1 i32.const 1 i32.add local.tee 1
//!     local.get 0 i32.lt_s
//!     br_if 0))
//! ```
//!
//! (the `br_if` pops the only value the loop's `(result i32)` needs) compiled
//! with exit 0 on ARM and RV32. Measured on 381c8432 over the pinned spec
//! suite's 2 719 `assert_invalid` modules x 3 backends = 8 157 compiles per
//! entry path: `--func-index 0` exits 0 on 1 803 of them and `--all-exports`
//! on 44 (most of these modules export nothing, so the whole-module path
//! stops at "No exported functions found" before it lowers anything). None
//! of the 16 314 is refused for being invalid, and 12 do not finish (below).
//!
//! Three tests.
//!
//! `curated_invalid_modules_are_refused_on_every_entry_path` runs in the
//! ordinary `cargo test`: the 13 fixtures of the retired Python pin table
//! (`type-empty-{i32,i64,f32,f64}` x `{block,loop,if}` from the suite, plus
//! the issue's module), on three backends and five CLI entry paths, plus the
//! two library decode entry points. Each has a paired VALID twin that must
//! still compile on the same path, so "refuses everything" cannot pass.
//!
//! `spec_assert_invalid_modules_are_all_refused` and
//! `spec_assert_malformed_modules_are_all_refused` are `#[ignore]`d because
//! they need the `tests/spec-testsuite` submodule, which the required Test
//! job does not check out. The Spec Suite workflow runs them with
//! `--ignored` and greps their exact counts. They are the issue's "suggested
//! gate": every `assert_invalid` / `assert_malformed` form in the suite goes
//! to `synth compile`.
//!
//! WHY EXIT CODE ALONE IS NOT THE VERDICT. The Python oracle this replaces
//! refused to run that census, for a good reason: before a validator existed,
//! a non-zero exit on most `assert_invalid` modules meant "synth does not
//! lower some op in it", so counting exits would have measured feature gaps.
//! Here a refusal counts only when stderr carries the validator's own
//! diagnostic ([`NEEDLE`]), so the number is the validator's.
//!
//! Set `SYNTH=/path/to/synth` to judge another binary (the red half: the
//! numbers above). The library legs always judge the tree the test was built
//! from.
//!
//! Exit codes, synth's own stderr and the presence of the output file only —
//! never disassembly text.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

use wast::lexer::Lexer;
use wast::parser::{self, ParseBuffer};
use wast::{QuoteWat, QuoteWatTest, Wast, WastDirective, Wat};

/// What every #1207 refusal says (`synth_core::wasm_decoder::INVALID_MODULE_NEEDLE`).
const NEEDLE: &str = synth_core::wasm_decoder::INVALID_MODULE_NEEDLE;
const ISSUE: &str = "#1207";

const BACKENDS: &[(&str, &[&str])] = &[
    ("arm", &["--cortex-m"]),
    ("riscv", &["-b", "riscv"]),
    ("aarch64", &["-b", "aarch64"]),
];

fn synth() -> PathBuf {
    match std::env::var_os("SYNTH") {
        Some(p) => PathBuf::from(p),
        None => PathBuf::from(env!("CARGO_BIN_EXE_synth")),
    }
}

fn scratch(tag: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-1207-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("scratch dir");
    dir
}

/// How one `synth compile` ended.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Verdict {
    /// Exit 0. For an invalid module this is the defect.
    Accepted,
    /// Non-zero exit, the validator's diagnostic, no output file.
    RefusedInvalid,
    /// Non-zero exit for some other stated reason, no output file.
    RefusedOther(String),
    /// Non-zero exit AND an output file: a refusal that still wrote an object.
    RefusedButWrote,
    /// Still running after [`COMPILE_TIMEOUT`]; killed.
    TimedOut,
}

/// A refusal takes milliseconds. The limit exists for the red half: the
/// pre-fix binary does not finish on four suite modules, on any backend. Two
/// are invalid (`(table 0xffff_ffff 0 funcref)` in table.wast and its
/// table64.wast twin, a table of four billion entries) and two are malformed
/// (binary.wast, "too many locals": four billion locals); it grows by
/// gigabytes for minutes on each.
const COMPILE_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(10);

fn compile(input: &Path, flags: &[&str], out: &Path) -> Verdict {
    let _ = std::fs::remove_file(out);
    // stderr goes to a file, not a pipe: nothing has to drain it while the
    // child is polled for the timeout.
    let err_path = out.with_extension("stderr");
    let mut child = Command::new(synth())
        .arg("compile")
        .arg(input)
        .args(flags)
        .arg("-o")
        .arg(out)
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(&err_path).expect("stderr file"))
        .spawn()
        .expect("run synth compile");
    let started = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("wait for synth") {
            break status;
        }
        if started.elapsed() > COMPILE_TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            let _ = std::fs::remove_file(out);
            let _ = std::fs::remove_file(&err_path);
            return Verdict::TimedOut;
        }
        std::thread::sleep(std::time::Duration::from_millis(2));
    };
    let wrote = out.exists();
    let _ = std::fs::remove_file(out);
    let err = std::fs::read(&err_path).unwrap_or_default();
    let _ = std::fs::remove_file(&err_path);
    if status.success() {
        return Verdict::Accepted;
    }
    if wrote {
        return Verdict::RefusedButWrote;
    }
    let err = String::from_utf8_lossy(&err);
    if err.contains(NEEDLE) && err.contains(ISSUE) {
        Verdict::RefusedInvalid
    } else {
        let last = err
            .lines()
            .rev()
            .find(|l| !l.trim().is_empty())
            .unwrap_or("");
        Verdict::RefusedOther(last.chars().take(160).collect())
    }
}

// ---------------------------------------------------------------------------
// Test 1: the curated fixtures, on every entry path.
// ---------------------------------------------------------------------------

/// (name, invalid function, valid twin). The twin differs only by producing
/// the value the invalid one leaves missing.
fn curated() -> Vec<(String, String, String)> {
    let mut v = Vec::new();
    for ty in ["i32", "i64", "f32", "f64"] {
        for ctor in ["block", "loop", "if"] {
            let (bad, good) = match ctor {
                "if" => (
                    "(if (i32.const 0) (then))".to_string(),
                    "(if (i32.const 0) (then))".to_string(),
                ),
                _ => (format!("({ctor})"), format!("({ctor})")),
            };
            v.push((
                format!("type-empty-{ctor}-{ty}"),
                format!(r#"(func (export "f") (result {ty}) {bad})"#),
                format!(r#"(func (export "f") (result {ty}) {good} ({ty}.const 0))"#),
            ));
        }
    }
    v.push((
        "cu_add_tee".to_string(),
        r#"(func (export "f") (param i32) (result i32) (local i32)
             (loop (result i32)
               local.get 1 i32.const 1 i32.add local.tee 1
               local.get 0 i32.lt_s
               br_if 0))"#
            .to_string(),
        // The same loop, with a value left for its declared result.
        r#"(func (export "f") (param i32) (result i32) (local i32)
             (loop (result i32)
               local.get 1 i32.const 1 i32.add local.tee 1
               local.get 0 i32.lt_s
               br_if 0
               local.get 1))"#
            .to_string(),
    ));
    v
}

/// The curated legs. ARM is cortex-m7dp here (single- and double-precision
/// FPU) so the f32 and f64 valid twins COMPILE and the control is not mostly
/// declines; the spec-suite tests below use the census's `--cortex-m`.
const CURATED_BACKENDS: &[(&str, &[&str])] = &[
    ("arm", &["--target", "cortex-m7dp"]),
    ("riscv", &["-b", "riscv"]),
    ("aarch64", &["-b", "aarch64"]),
];

/// An unrelated valid module, for the multi-module `.wast` path.
const OTHER_MODULE: &str = r#"(module (func (export "g") (result i32) (i32.const 7)))"#;

struct EntryPath {
    name: &'static str,
    ext: &'static str,
    /// Wraps one function into the file's text.
    wrap: fn(&str) -> String,
    flags: &'static [&'static str],
}

const ENTRY_PATHS: &[EntryPath] = &[
    EntryPath {
        name: "whole module (--all-exports)",
        ext: "wat",
        wrap: |f| format!("(module {f})"),
        flags: &["--all-exports"],
    },
    EntryPath {
        name: "single function (--func-name)",
        ext: "wat",
        wrap: |f| format!("(module {f})"),
        flags: &["--func-name", "f"],
    },
    EntryPath {
        name: "single function (--func-index)",
        ext: "wat",
        wrap: |f| format!("(module {f})"),
        flags: &["--func-index", "0"],
    },
    EntryPath {
        name: "single-module .wast",
        ext: "wast",
        wrap: |f| format!("(module {f})"),
        flags: &["--all-exports"],
    },
    // The merge decodes every module and SKIPS one whose decode fails; an
    // invalid module must refuse the compile, not be passed over. The
    // invalid module is listed FIRST so that "skip it and compile the other"
    // would still write an object.
    EntryPath {
        name: "multi-module .wast (--all-exports)",
        ext: "wast",
        wrap: |f| format!("(module {f})\n{OTHER_MODULE}\n"),
        flags: &["--all-exports"],
    },
    // The single-function extraction picks the first module that decodes
    // with exports, which is the invalid one here.
    EntryPath {
        name: "multi-module .wast (--func-name)",
        ext: "wast",
        wrap: |f| format!("(module {f})\n{OTHER_MODULE}\n"),
        flags: &["--func-name", "f"],
    },
];

#[test]
fn curated_invalid_modules_are_refused_on_every_entry_path() {
    let dir = scratch("curated");
    let fixtures = curated();
    assert_eq!(fixtures.len(), 13);
    let mut refused = 0usize;
    let mut control_ok = 0usize;
    let mut control_declined = 0usize;
    let mut wrong = Vec::new();
    let mut declined_at = Vec::new();

    for (name, bad, good) in &fixtures {
        // The fixtures prove nothing unless they are what they claim to be.
        let bad_bytes = wat::parse_str(format!("(module {bad})")).expect("fixture encodes");
        let good_bytes = wat::parse_str(format!("(module {good})")).expect("twin encodes");
        assert!(
            wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM1)
                .validate_all(&bad_bytes)
                .is_err(),
            "{name}: the fixture VALIDATES, so it proves nothing"
        );
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM1)
            .validate_all(&good_bytes)
            .unwrap_or_else(|e| panic!("{name}: the valid twin does not validate: {e}"));

        // Library entry points: no `synth` binary involved.
        for (what, r) in [
            (
                "decode_wasm_module",
                synth_core::decode_wasm_module(&bad_bytes).map(|_| ()),
            ),
            (
                "decode_wasm_functions",
                synth_core::decode_wasm_functions(&bad_bytes).map(|_| ()),
            ),
            (
                "validate_core_module",
                synth_core::validate_core_module(&bad_bytes),
            ),
        ] {
            match r {
                Ok(()) => wrong.push(format!("{name} / library {what}: ACCEPTED")),
                Err(e) if format!("{e:#}").contains(NEEDLE) => refused += 1,
                Err(e) => wrong.push(format!("{name} / library {what}: refused, but as {e:#}")),
            }
        }
        synth_core::decode_wasm_module(&good_bytes)
            .unwrap_or_else(|e| panic!("{name}: library refuses the valid twin: {e:#}"));
        synth_core::decode_wasm_functions(&good_bytes)
            .unwrap_or_else(|e| panic!("{name}: library refuses the valid twin: {e:#}"));

        for (be, be_flags) in CURATED_BACKENDS {
            for path in ENTRY_PATHS {
                let flags: Vec<&str> = be_flags.iter().chain(path.flags).copied().collect();
                let out = dir.join("m.o");
                let src = dir.join(format!("bad.{}", path.ext));
                std::fs::write(&src, (path.wrap)(bad)).expect("write");
                match compile(&src, &flags, &out) {
                    Verdict::RefusedInvalid => refused += 1,
                    v => wrong.push(format!("{name} / {be} / {}: {v:?}", path.name)),
                }
                // Paired control: the valid twin on the same path. It must
                // never be refused AS INVALID. Whether it compiles is the
                // backend's own reach (an f32 function on a core with no FPU
                // declines by name), counted and pinned below.
                let src = dir.join(format!("good.{}", path.ext));
                std::fs::write(&src, (path.wrap)(good)).expect("write");
                match compile(&src, &flags, &out) {
                    Verdict::Accepted => control_ok += 1,
                    Verdict::RefusedOther(why) => {
                        control_declined += 1;
                        declined_at.push(format!("{name} / {be} / {}: {why}", path.name));
                    }
                    v => wrong.push(format!("{name} / {be} / {} VALID TWIN: {v:?}", path.name)),
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);

    println!(
        "ORACLE invalid-1207 curated: {refused} refusals of {} ({} fixtures x ({} backends x {} entry paths + 3 library entry points)); \
         valid twins: {control_ok} compile, {control_declined} declined for a stated non-validation reason, 0 refused as invalid",
        fixtures.len() * (CURATED_BACKENDS.len() * ENTRY_PATHS.len() + 3),
        fixtures.len(),
        CURATED_BACKENDS.len(),
        ENTRY_PATHS.len(),
    );
    if (control_ok, control_declined) != CURATED_CONTROL {
        for d in &declined_at {
            println!("  control declined: {d}");
        }
    }
    assert!(
        wrong.is_empty(),
        "{} wrong verdict(s):\n  {}",
        wrong.len(),
        wrong.join("\n  ")
    );
    assert_eq!(refused, 13 * (3 * 6 + 3));
    // Exact, so the control cannot quietly turn into "declines everything".
    assert_eq!((control_ok, control_declined), CURATED_CONTROL);
}

/// (valid twins that compile, valid twins declined for a non-validation
/// reason) over 13 fixtures x 3 backends x 6 entry paths = 234. The 57
/// declines, all by name: 30 are the six f32/f64 twins on RV32, which has no
/// float lowering (five entry paths; the sixth is counted next); 27 are the
/// nine i64/f32/f64 twins on the multi-module merge of each backend, which
/// refuses a retained function with a non-i32 parameter or result (#1225).
const CURATED_CONTROL: (usize, usize) = (177, 57);

// ---------------------------------------------------------------------------
// Tests 2 and 3: the spec suite.
// ---------------------------------------------------------------------------

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

/// The suite's top level (the merged standard) and the one proposal
/// directory synth accepts on purpose. The other proposal directories are
/// forks of OLDER spec states (threads still asserts "multiple memories"
/// invalid, which WebAssembly 3.0 made valid) or proposals synth does not
/// claim.
fn suite_files() -> Vec<PathBuf> {
    let suite = repo_root().join("tests/spec-testsuite");
    let mut files = Vec::new();
    for dir in [suite.clone(), suite.join("proposals/custom-page-sizes")] {
        let mut here: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| {
                panic!(
                    "{}: {e} — is the submodule checked out? (git submodule update --init)",
                    dir.display()
                )
            })
            .map(|e| e.expect("dir entry").path())
            .filter(|p| p.extension().is_some_and(|e| e == "wast"))
            .collect();
        here.sort();
        files.extend(here);
    }
    files
}

const SUITE_FILES: usize = 257 + 4;

enum Form {
    Binary(Vec<u8>),
    /// A `(module quote ...)` whose text does not encode: fed as `.wat`.
    Text(Vec<u8>),
}

struct Case {
    at: String,
    form: Form,
}

#[derive(Default)]
struct Suite {
    invalid: Vec<Case>,
    malformed: Vec<Case>,
    /// Top-level `(module ...)` directives: must validate (the control).
    modules: Vec<Case>,
}

fn core_form(module: &mut QuoteWat<'_>) -> Option<Form> {
    if matches!(
        module,
        QuoteWat::Wat(Wat::Component(_)) | QuoteWat::QuoteComponent(..)
    ) {
        return None;
    }
    let quoted = matches!(module, QuoteWat::QuoteModule(..));
    Some(match module.to_test() {
        Ok(QuoteWatTest::Binary(b)) => Form::Binary(b),
        Ok(QuoteWatTest::Text(t)) => Form::Text(t),
        // A text module the encoder itself rejects has no bytes to feed.
        Err(e) => {
            assert!(!quoted);
            panic!("a non-quoted module failed to encode: {e}")
        }
    })
}

fn load_suite() -> Suite {
    let files = suite_files();
    assert_eq!(
        files.len(),
        SUITE_FILES,
        "the suite has {} .wast files, expected {SUITE_FILES} (empty submodule, or the pin moved)",
        files.len()
    );
    let mut suite = Suite::default();
    for f in &files {
        let text = std::fs::read_to_string(f).expect("read .wast");
        let name = f.file_name().unwrap().to_string_lossy().to_string();
        // names.wast carries a deliberately confusing U+202E identifier.
        let mut lexer = Lexer::new(&text);
        lexer.allow_confusing_unicode(true);
        let buf = ParseBuffer::new_with_lexer(lexer).unwrap_or_else(|e| panic!("{name}: lex: {e}"));
        let wast: Wast = parser::parse(&buf).unwrap_or_else(|e| panic!("{name}: parse: {e}"));
        for d in wast.directives {
            // `well_formed`: an assert_invalid or top-level module written
            // as `(module quote ...)` is well-formed text, so it has a
            // binary; only assert_malformed text is fed as text.
            let (bucket, span, mut module, well_formed) = match d {
                WastDirective::AssertInvalid { span, module, .. } => {
                    (&mut suite.invalid, span, module, true)
                }
                WastDirective::AssertMalformed { span, module, .. } => {
                    (&mut suite.malformed, span, module, false)
                }
                WastDirective::Module(module) => {
                    let span = module.span();
                    (&mut suite.modules, span, module, true)
                }
                _ => continue,
            };
            let (line, _) = span.linecol_in(&text);
            let at = format!("{name}:{}", line + 1);
            let Some(form) = core_form(&mut module) else {
                continue;
            };
            let form = match form {
                Form::Text(t) if well_formed => Form::Binary(
                    wat::parse_bytes(&t)
                        .unwrap_or_else(|e| panic!("{at}: quoted module does not encode: {e}"))
                        .into_owned(),
                ),
                other => other,
            };
            bucket.push(Case { at, form });
        }
    }
    suite
}

/// Compiles every case on every backend, in parallel. Returns one verdict
/// per (case, backend), in case order.
fn compile_all(tag: &str, cases: &[Case], entry: &[&str]) -> Vec<[Verdict; 3]> {
    let dir = scratch(tag);
    let next = AtomicUsize::new(0);
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    let mut out: Vec<Option<[Verdict; 3]>> = vec![None; cases.len()];
    let results = std::sync::Mutex::new(&mut out);
    std::thread::scope(|s| {
        for w in 0..workers {
            let (dir, next, results) = (&dir, &next, &results);
            s.spawn(move || {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some(case) = cases.get(i) else { break };
                    let (src, bytes) = match &case.form {
                        Form::Binary(b) => (dir.join(format!("w{w}.wasm")), b),
                        Form::Text(t) => (dir.join(format!("w{w}.wat")), t),
                    };
                    std::fs::write(&src, bytes).expect("write case");
                    let obj = dir.join(format!("w{w}.o"));
                    let v = [0, 1, 2].map(|b| {
                        let flags: Vec<&str> = BACKENDS[b].1.iter().chain(entry).copied().collect();
                        compile(&src, &flags, &obj)
                    });
                    results.lock().unwrap()[i] = Some(v);
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&dir);
    out.into_iter()
        .map(|v| v.expect("every case ran"))
        .collect()
}

/// `assert_invalid` core modules in the suite: 2700 at the top level, 19 in
/// custom-page-sizes.
const INVALID_MODULES: usize = 2700 + 19;
/// Top-level `(module ...)` directives, the validity control.
const VALID_MODULES: usize = 2230;
/// `assert_malformed` modules: (binary form, quoted text form).
const MALFORMED_MODULES: (usize, usize) = (712, 1233);

#[test]
#[ignore = "needs the tests/spec-testsuite submodule; run by the Spec Suite workflow with --ignored"]
fn spec_assert_invalid_modules_are_all_refused() {
    let suite = load_suite();
    let n = suite.invalid.len();

    // Library leg, and the fixtures' own ground truth: every case is a
    // BINARY the validator rejects, and both decode entry points refuse it.
    let mut lib_wrong = Vec::new();
    for c in &suite.invalid {
        let Form::Binary(b) = &c.form else {
            panic!("{}: an assert_invalid module with no binary form", c.at)
        };
        for (what, r) in [
            (
                "decode_wasm_module",
                synth_core::decode_wasm_module(b).map(|_| ()),
            ),
            (
                "decode_wasm_functions",
                synth_core::decode_wasm_functions(b).map(|_| ()),
            ),
        ] {
            match r {
                Err(e) if format!("{e:#}").contains(NEEDLE) => {}
                Err(e) => lib_wrong.push(format!("{} {what}: refused, but as {e:#}", c.at)),
                Ok(()) => lib_wrong.push(format!("{} {what}: ACCEPTED", c.at)),
            }
        }
    }

    // The control: every top-level module of the suite validates, so the
    // validator's feature set rejects nothing the standard accepts.
    let mut control_wrong = Vec::new();
    for c in &suite.modules {
        let Form::Binary(b) = &c.form else {
            panic!("{}: a top-level module with no binary form", c.at)
        };
        if let Err(e) = synth_core::validate_core_module(b) {
            control_wrong.push(format!("{}: {e:#}", c.at));
        }
    }

    // CLI legs: the whole-module path and the single-function path. Most
    // assert_invalid modules export nothing, so before the fix
    // `--all-exports` exited non-zero on them for an unrelated reason ("No
    // exported functions found"); `--func-index 0` asks for a function by
    // index and is where the pre-fix binary compiles the most.
    let mut wrong = Vec::new();
    for (leg, entry) in [
        ("--all-exports", &["--all-exports"][..]),
        ("--func-index 0", &["--func-index", "0"][..]),
    ] {
        let verdicts = compile_all("invalid", &suite.invalid, entry);
        let mut accepted = [0usize; 3];
        let mut refused = [0usize; 3];
        let mut timed_out = 0usize;
        for (c, v) in suite.invalid.iter().zip(&verdicts) {
            for b in 0..3 {
                match &v[b] {
                    Verdict::RefusedInvalid => refused[b] += 1,
                    other => {
                        match other {
                            Verdict::Accepted => accepted[b] += 1,
                            Verdict::TimedOut => timed_out += 1,
                            _ => {}
                        }
                        wrong.push(format!("{} / {} {leg}: {other:?}", c.at, BACKENDS[b].0));
                    }
                }
            }
        }
        println!(
            "ORACLE invalid-1207 spec {leg}: {} of {} assert_invalid compiles refused as invalid ({n} modules x 3 backends), {} accepted, {timed_out} timed out",
            refused.iter().sum::<usize>(),
            n * 3,
            accepted.iter().sum::<usize>(),
        );
        for b in 0..3 {
            println!(
                "ORACLE invalid-1207 spec {leg} [{}]: {} refused as invalid, {} accepted, {} other",
                BACKENDS[b].0,
                refused[b],
                accepted[b],
                n - refused[b] - accepted[b],
            );
        }
    }
    println!(
        "ORACLE invalid-1207 library: {} of {} assert_invalid decodes refused as invalid (2 entry points)",
        n * 2 - lib_wrong.len(),
        n * 2,
    );
    println!(
        "ORACLE invalid-1207 control: {} of {} top-level spec modules validate",
        suite.modules.len() - control_wrong.len(),
        suite.modules.len(),
    );
    for w in wrong.iter().take(40) {
        println!("  WRONG {w}");
    }
    assert!(
        wrong.is_empty(),
        "{} of {} assert_invalid compiles were not refused as invalid (first 40 above)",
        wrong.len(),
        n * 6
    );
    assert!(lib_wrong.is_empty(), "library: {lib_wrong:#?}");
    assert!(control_wrong.is_empty(), "control: {control_wrong:#?}");
    assert_eq!(n, INVALID_MODULES);
    assert_eq!(suite.modules.len(), VALID_MODULES);
}

#[test]
#[ignore = "needs the tests/spec-testsuite submodule; run by the Spec Suite workflow with --ignored"]
fn spec_assert_malformed_modules_are_all_refused() {
    let suite = load_suite();
    let binary = suite
        .malformed
        .iter()
        .filter(|c| matches!(c.form, Form::Binary(_)))
        .count();
    let text = suite.malformed.len() - binary;

    let verdicts = compile_all("malformed", &suite.malformed, &["--all-exports"]);
    let mut accepted = 0usize;
    let mut timed_out = 0usize;
    let mut by_validator = 0usize;
    let mut by_other = 0usize;
    let mut wrong = Vec::new();
    for (c, v) in suite.malformed.iter().zip(&verdicts) {
        for b in 0..3 {
            match &v[b] {
                Verdict::RefusedInvalid => by_validator += 1,
                Verdict::RefusedOther(_) => by_other += 1,
                other => {
                    match other {
                        Verdict::Accepted => accepted += 1,
                        Verdict::TimedOut => timed_out += 1,
                        _ => {}
                    }
                    wrong.push(format!("{} / {}: {other:?}", c.at, BACKENDS[b].0));
                }
            }
        }
    }
    println!(
        "ORACLE malformed-1207 spec: {} of {} assert_malformed compiles refused ({binary} binary + {text} text modules x 3 backends), {accepted} accepted, {timed_out} timed out",
        by_validator + by_other,
        suite.malformed.len() * 3,
    );
    println!(
        "ORACLE malformed-1207 spec: {by_validator} refused by the validator, {by_other} by the text or binary reader"
    );
    for w in wrong.iter().take(40) {
        println!("  WRONG {w}");
    }
    assert!(
        wrong.is_empty(),
        "{} assert_malformed compiles were not refused (first 40 above)",
        wrong.len()
    );
    assert_eq!((binary, text), MALFORMED_MODULES);
}
