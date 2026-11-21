//! `target-record` — write synth's half of North Star O1 as
//! `north-star-input.O1.json` (RQ-91-TARGETRECORD, Refs #1741; consumer seam
//! pulseengine.eu#393, asset name pulseengine.eu#394, consumer
//! pulseengine.eu#396 `tools/north-star-measure`).
//!
//! ONE command, every number executed in this run:
//!
//! ```text
//! SYNTH=target/debug/synth cargo run -p synth-oracle --features exec \
//!     --bin target-record -- --out north-star-input.O1.json
//! ```
//!
//! Targets: cortex-m4 and cortex-m7dp, the two rows Bet B names. Per target,
//! four facts, never summed:
//!
//! - `reach`: every top-level `.wast` of the spec testsuite submodule at its
//!   pinned gitlink (257 files), compiled with `--all-exports`; a file counts
//!   when synth exits 0 with every export compiled (the compile census's `ok`
//!   bucket). `value.fraction` is the number. `pass` is a REGRESSION GATE
//!   against the floor measured at this lane's commit, NOT a reach threshold,
//!   and the fact says so. The corpus was chosen by the project, not by a
//!   consumer. It must be a git checkout at the pinned gitlink.
//! - `execution_match`: the PROBE SET (`synth_oracle::probes`, 21 probes x
//!   144 vector pairs = 3024 vectors) compiled to the self-contained image,
//!   booted through its own `Reset_Handler` with the boot contract asserted
//!   (R10/R11 against `__linear_memory_base`, SP against the vector table, the
//!   `blx r0` target a function symbol), on the target's unicorn model
//!   (Cortex-M4 / Cortex-M7, read back), every case judged against kiln.
//! - `wcet`: the `--emit-wcet` sidecar of that compile. Each bound is
//!   cross-checked against the worst executed call of its function PRICED IN
//!   CYCLES (`synth_oracle::cycles`, Cortex-M4 TRM table), and the bounded
//!   count must reach its floor.
//! - `hardware_run`: always `ran: false`. synth runs no silicon.
//!
//! Each executed fact carries a negative control from THIS run: an empty
//! corpus (reach); a planted wrong reference and a planted undefined
//! instruction (execution); a bound planted one cycle below the priced cost
//! (wcet). A control that does not turn its fact red fails the fact; a fact
//! with no control says so.
//!
//! Before anything is written the record is checked against the vendored
//! consumer schema, for completeness (four facts per requested target, `pass`
//! implies `ran`) and for its file name (`north-star-input.<objective>.json`).
//! The process exits 0 when such a record was written, WHATEVER the facts say;
//! `--require-pass <id>` (repeatable) turns a named fact's failure into exit 1.
//! `--targets` writes a subset only together with `--partial`.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use synth_oracle::compare::{EmuOutcome, RefOutcome, Verdict, verdict};
use synth_oracle::emulate::Cpu;
use synth_oracle::image::BootedImage;
use synth_oracle::probes::{AGREE_PROBES, PROBES_WAT, VECTORS};
use synth_oracle::record::{
    self, Control, ExecCounts, Fact, ReachCounts, Record, execution_fact, hardware_fact,
    reach_fact, summarize_wcet, wcet_fact,
};
use synth_oracle::reference::{self, Imports};
use synth_oracle::synth::synth_binary;
use synth_oracle::value::{WasmValue, export_signature};

const FUEL: u64 = 1_000_000;
const BUDGET: usize = 1_000_000;

/// One synth compile may take this long; a hang is killed and counted.
const COMPILE_TIMEOUT: Duration = Duration::from_secs(120);

/// The spec testsuite's top-level `.wast` count at the pinned gitlink (the
/// same 257 the compile census pins as EXPECTED_WAST_FILES).
const SPEC_FILES: u64 = 257;

/// Executed-vector floor per target: every AGREE probe x every vector pair
/// (21 x 12 x 12). Set to the measured count; never lowered to make a run
/// green.
const EXEC_FLOOR: u64 = 3024;

/// Where the reach and wcet floors were measured.
const FLOORS_SET_AT: &str = "synth 0.90.0 on the v092-stack2 lane stack (commit 7537385)";

struct Target {
    name: &'static str,
    flags: &'static [&'static str],
    cpu: Cpu,
    fpu: bool,
    /// Reach floor: the `ok` count MEASURED at [`FLOORS_SET_AT`]. cortex-m4
    /// 16 and cortex-m7dp 26 of 257, equal to the compile census's `arm` and
    /// `arm_m7dp` `ok` pins. Raised when reach rises; never lowered to make a
    /// run green.
    reach_floor: u64,
    /// Bounded-function floor over the probe image's 22 functions, measured
    /// at [`FLOORS_SET_AT`]: cortex-m4 20 (the two loops decline). `None`:
    /// no sound cycle model for the core (Cortex-M7), so the fact cannot pass.
    wcet_floor: Option<u64>,
}

const TARGETS: &[Target] = &[
    Target {
        name: "cortex-m4",
        flags: &["--target", "cortex-m4"],
        cpu: Cpu::CortexM4,
        fpu: false,
        reach_floor: 16,
        wcet_floor: Some(20),
    },
    Target {
        name: "cortex-m7dp",
        flags: &["--target", "cortex-m7dp"],
        cpu: Cpu::CortexM7,
        fpu: true,
        reach_floor: 26,
        wcet_floor: None,
    },
];

struct Args {
    out: PathBuf,
    spec_dir: PathBuf,
    work: PathBuf,
    /// The work directory was chosen here, so it is removed at the end.
    work_is_temp: bool,
    version: Option<String>,
    evidence: String,
    targets: Vec<String>,
    partial: bool,
    require_pass: Vec<String>,
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        out: PathBuf::from("north-star-input.O1.json"),
        spec_dir: workspace_root().join("tests/spec-testsuite"),
        work: std::env::temp_dir().join(format!("synth-target-record-{}", std::process::id())),
        work_is_temp: true,
        version: None,
        evidence: default_evidence(),
        targets: TARGETS.iter().map(|t| t.name.to_string()).collect(),
        partial: false,
        require_pass: Vec::new(),
    };
    let mut subset = false;
    let mut it = std::env::args().skip(1);
    while let Some(k) = it.next() {
        let mut v = || it.next().ok_or_else(|| format!("{k} needs a value"));
        match k.as_str() {
            "--out" => a.out = v()?.into(),
            "--spec-dir" => a.spec_dir = v()?.into(),
            "--work" => {
                a.work = v()?.into();
                a.work_is_temp = false;
            }
            "--version" => a.version = Some(v()?),
            "--evidence" => a.evidence = v()?,
            "--targets" => {
                a.targets = v()?.split(',').map(str::to_string).collect();
                subset = true;
            }
            "--partial" => a.partial = true,
            "--require-pass" => a.require_pass.push(v()?),
            "-h" | "--help" => {
                println!(
                    "target-record [--out north-star-input.O1.json] [--spec-dir D] [--work D] \
                     [--version X.Y.Z] [--evidence URL] [--targets a,b --partial] \
                     [--require-pass ID]..."
                );
                std::process::exit(0);
            }
            other => return Err(format!("unknown argument {other}")),
        }
    }
    for t in &a.targets {
        if !TARGETS.iter().any(|x| x.name == t) {
            return Err(format!("unknown target {t}"));
        }
    }
    let all = TARGETS
        .iter()
        .all(|t| a.targets.iter().any(|x| x == t.name));
    if subset && !all && !a.partial {
        return Err(
            "--targets names a subset: a partial record is written only with --partial".into(),
        );
    }
    Ok(a)
}

fn default_evidence() -> String {
    match (
        std::env::var("GITHUB_SERVER_URL"),
        std::env::var("GITHUB_REPOSITORY"),
        std::env::var("GITHUB_RUN_ID"),
    ) {
        (Ok(s), Ok(r), Ok(id)) => format!("{s}/{r}/actions/runs/{id}"),
        _ => "local run: no CI URL".to_string(),
    }
}

fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let o = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .ok()?;
    o.status
        .success()
        .then(|| String::from_utf8_lossy(&o.stdout).trim().to_string())
}

/// The version the record is keyed by (REVIEW_17 finding 5). On the release
/// tag itself it is the tag's version (`0.90.0`); anywhere else it is the
/// git description as build metadata (`0.90.0+53-g1a2b914186c5`, `-dirty`
/// when the tree is modified), never the last tag's version alone. Without
/// any reachable tag (a shallow checkout) it is the workspace version with
/// `+g<sha>`. `--version` overrides, for the release job.
fn derive_version(describe: Option<&str>, head: Option<&str>) -> String {
    let pkg = env!("CARGO_PKG_VERSION");
    match describe.and_then(|d| d.strip_prefix('v')) {
        Some(d) => match d.split_once('-') {
            None => d.to_string(),
            Some((tag, rest)) => format!("{tag}+{rest}"),
        },
        None => match head {
            Some(h) => format!("{pkg}+g{}", &h[..h.len().min(12)]),
            None => format!("{pkg}+unknown"),
        },
    }
}

/// `synth compile`, killed after [`COMPILE_TIMEOUT`].
/// `(succeeded with output, combined text, timed out)`.
fn synth(input: &Path, flags: &[&str], out: &Path) -> Result<(bool, String, bool), String> {
    let bin = synth_binary()?;
    let err_path = out.with_extension("stderr");
    let errf = std::fs::File::create(&err_path).map_err(|e| e.to_string())?;
    let mut child = Command::new(&bin)
        .arg("compile")
        .arg(input)
        .args(flags)
        .arg("-o")
        .arg(out)
        .env("RUST_LOG", "error")
        .stdout(Stdio::null())
        .stderr(errf)
        .spawn()
        .map_err(|e| format!("{}: {e}", bin.display()))?;
    let start = Instant::now();
    let status = loop {
        if let Some(st) = child.try_wait().map_err(|e| e.to_string())? {
            break Some(st);
        }
        if start.elapsed() > COMPILE_TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let text = std::fs::read_to_string(&err_path).unwrap_or_default();
    let _ = std::fs::remove_file(&err_path);
    Ok(match status {
        Some(st) => (st.success() && out.is_file(), text, false),
        None => (false, text, true),
    })
}

// ------------------------------------------------------------------ reach --

fn wast_files(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wast") && p.is_file())
        .collect();
    v.sort();
    v
}

fn run_reach(files: &[PathBuf], flags: &[&str], work: &Path) -> Result<ReachCounts, String> {
    std::fs::create_dir_all(work).map_err(|e| e.to_string())?;
    let jobs = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(2)
        .clamp(1, 8);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results: std::sync::Mutex<Vec<(bool, bool, bool)>> = std::sync::Mutex::new(Vec::new());
    let err: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);
    std::thread::scope(|s| {
        for _ in 0..jobs {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(f) = files.get(i) else { break };
                    let out = work.join(format!("reach-{i}.elf"));
                    let mut fl: Vec<&str> = flags.to_vec();
                    fl.push("--all-exports");
                    match synth(f, &fl, &out) {
                        Ok((ok, text, timeout)) => {
                            let _ = std::fs::remove_file(&out);
                            if timeout {
                                eprintln!("  TIMEOUT {}", f.display());
                            }
                            results
                                .lock()
                                .unwrap()
                                .push((ok, text.contains("panicked"), timeout));
                        }
                        Err(e) => {
                            *err.lock().unwrap() = Some(e);
                            break;
                        }
                    }
                }
            });
        }
    });
    if let Some(e) = err.into_inner().unwrap() {
        return Err(e);
    }
    let r = results.into_inner().unwrap();
    Ok(ReachCounts {
        files: files.len() as u64,
        compiled: r.iter().filter(|x| x.0).count() as u64,
        panics: r.iter().filter(|x| x.1).count() as u64,
        timeouts: r.iter().filter(|x| x.2).count() as u64,
        corpus_mismatch: None,
    })
}

// -------------------------------------------------------------- execution --

fn pairs() -> Vec<[WasmValue; 2]> {
    VECTORS
        .iter()
        .flat_map(|&a| {
            VECTORS
                .iter()
                .map(move |&b| [WasmValue::I32(a), WasmValue::I32(b)])
        })
        .collect()
}

/// kiln's outcome for every AGREE probe x pair, computed once.
fn references(wasm: &[u8]) -> Result<Vec<(String, [WasmValue; 2], RefOutcome)>, String> {
    let mut v = Vec::new();
    for p in AGREE_PROBES {
        for args in pairs() {
            let r = reference::run(wasm, p, &args, FUEL, &Imports::new())
                .map_err(|e| format!("kiln {p}{args:?}: {e:?}"))?;
            v.push((p.to_string(), args, r.outcome));
        }
    }
    Ok(v)
}

struct ExecResult {
    counts: ExecCounts,
    /// function -> worst priced cost of one judged call, in cycles.
    max_cycles: BTreeMap<String, u64>,
    /// function -> why a judged call could not be priced.
    unpriced: BTreeMap<String, String>,
    traps: u64,
    trap_paths: BTreeMap<String, u64>,
}

fn sweep(
    img: &mut BootedImage,
    wasm: &[u8],
    refs: &[(String, [WasmValue; 2], RefOutcome)],
) -> Result<ExecResult, String> {
    let mut c = ExecCounts::default();
    let mut max_cycles: BTreeMap<String, u64> = BTreeMap::new();
    let mut unpriced: BTreeMap<String, String> = BTreeMap::new();
    let mut traps = 0;
    let mut trap_paths: BTreeMap<String, u64> = BTreeMap::new();
    for (p, args, r) in refs {
        let sig = export_signature(wasm, p)?;
        let run = match img.call(p, &sig, args, BUDGET) {
            Ok(run) => run,
            Err(e) => {
                eprintln!("  refused {p}{args:?}: {e:?}");
                c.refused += 1;
                continue;
            }
        };
        match verdict(r, &run.outcome) {
            Verdict::Agree => {
                c.executed += 1;
                c.matched += 1;
            }
            Verdict::Disagree(why) => {
                c.executed += 1;
                c.wrong += 1;
                if c.wrong <= 10 {
                    eprintln!(
                        "  WRONG {p}{args:?}: {why} (ref {r:?}, emu {:?})",
                        run.outcome
                    );
                }
            }
            Verdict::Inconclusive(why) => {
                c.inconclusive += 1;
                eprintln!("  inconclusive {p}{args:?}: {why}");
                continue;
            }
        }
        if let (RefOutcome::Trap { .. }, EmuOutcome::Trap { insn, .. }) = (r, &run.outcome) {
            traps += 1;
            *trap_paths.entry(insn.clone()).or_default() += 1;
        }
        match run.cycles {
            Ok(cy) => {
                let m = max_cycles.entry(p.clone()).or_default();
                *m = (*m).max(cy);
            }
            Err(e) => {
                unpriced.entry(p.clone()).or_insert(e);
            }
        }
    }
    // A function with ANY unpriced call has no trustworthy worst case.
    for p in unpriced.keys() {
        max_cycles.remove(p);
    }
    Ok(ExecResult {
        counts: c,
        max_cycles,
        unpriced,
        traps,
        trap_paths,
    })
}

/// The execution leg's two planted controls, each on a FRESH boot of the
/// same image. True only when both turned red.
fn execution_controls(
    elf: &Path,
    cpu: Cpu,
    fpu: bool,
    wasm: &[u8],
) -> Result<(bool, Value), String> {
    let sig = export_signature(wasm, "add")?;
    // (a) A wrong reference: kiln runs `add` as SUB.
    let planted = PROBES_WAT.replacen(
        "(func (export \"add\") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)",
        "(func (export \"add\") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)",
        1,
    );
    if planted == PROBES_WAT {
        return Err("the planted reference did not change the module".into());
    }
    let pw = wat::parse_str(&planted).map_err(|e| e.to_string())?;
    let mut img = BootedImage::boot(elf, cpu, fpu).map_err(|e| format!("{e:?}"))?;
    let mut disagree = 0u64;
    for args in pairs() {
        let r = reference::run(&pw, "add", &args, FUEL, &Imports::new())
            .map_err(|e| format!("{e:?}"))?;
        let e = img
            .call("add", &sig, &args, BUDGET)
            .map_err(|e| format!("{e:?}"))?;
        if matches!(verdict(&r.outcome, &e.outcome), Verdict::Disagree(_)) {
            disagree += 1;
        }
    }
    // add == sub exactly when b is 0 or 0x80000000.
    let expected = (VECTORS.len() * (VECTORS.len() - 2)) as u64;
    let a_red = disagree == expected;
    // (b) A planted undefined instruction at the entry of `add`.
    let mut img = BootedImage::boot(elf, cpu, fpu).map_err(|e| format!("{e:?}"))?;
    let (addr, _) = img.funcs()["add"];
    img.patch(addr, &[0xFF, 0xFF, 0xFF, 0xFF])
        .map_err(|e| format!("{e:?}"))?;
    let args = [WasmValue::I32(2), WasmValue::I32(3)];
    let r =
        reference::run(wasm, "add", &args, FUEL, &Imports::new()).map_err(|e| format!("{e:?}"))?;
    let e = img
        .call("add", &sig, &args, BUDGET)
        .map_err(|e| format!("{e:?}"))?;
    let b_red = matches!(verdict(&r.outcome, &e.outcome), Verdict::Disagree(_));
    Ok((
        a_red && b_red,
        json!({
            "planted_wrong_reference": {"disagreements": disagree, "expected": expected, "red": a_red},
            "planted_undefined_instruction": {"outcome": format!("{:?}", e.outcome), "red": b_red},
        }),
    ))
}

fn read_sidecar(elf: &Path) -> Option<Value> {
    let mut p = elf.as_os_str().to_owned();
    p.push(".wcet.json");
    let s = std::fs::read_to_string(PathBuf::from(p)).ok()?;
    serde_json::from_str(&s).ok()
}

/// The wcet control: `add` replaced by a bound ONE CYCLE below its priced
/// cost, which the cycle cross-check must reject. `None` when it cannot be
/// planted (no sidecar, `add` never priced): stated, never claimed.
fn wcet_control(sidecar: Option<&Value>, max_cycles: &BTreeMap<String, u64>) -> (Control, Value) {
    let Some(&cost) = max_cycles.get("add") else {
        return (None, json!("no control: `add` has no priced executed call"));
    };
    let Some(mut planted) = sidecar.cloned() else {
        return (None, json!("no control: no sidecar"));
    };
    let Some(funcs) = planted.get_mut("functions").and_then(Value::as_array_mut) else {
        return (None, json!("no control: sidecar has no functions"));
    };
    let Some(f) = funcs
        .iter_mut()
        .find(|f| f.get("name").and_then(Value::as_str) == Some("add"))
    else {
        return (None, json!("no control: `add` is not in the sidecar"));
    };
    let bound = cost.saturating_sub(1);
    *f = json!({"status": "bounded", "name": "add", "cycles": bound});
    let s = summarize_wcet(Some(&planted), max_cycles);
    // Judged by the cross-check alone: that is what this control tests.
    let red = s.below_executed.iter().any(|b| b.starts_with("add:"));
    (
        Some(red),
        json!({"planted_bound_for_add": bound, "priced_cost_of_add": cost, "red": red}),
    )
}

// ------------------------------------------------------------------- main --

fn main() {
    match run() {
        Ok(code) => std::process::exit(code),
        Err(e) => {
            eprintln!("target-record: {e}");
            std::process::exit(2);
        }
    }
}

fn run() -> Result<i32, String> {
    let a = parse_args()?;
    // Refuse a mismatched name BEFORE the run, and again below against the
    // record's own objective field before anything is written.
    record::check_file_name(&a.out, record::OBJECTIVE)?;
    std::fs::create_dir_all(&a.work).map_err(|e| e.to_string())?;
    let r = measure(&a);
    if a.work_is_temp {
        let _ = std::fs::remove_dir_all(&a.work);
    }
    r
}

fn measure(a: &Args) -> Result<i32, String> {
    let synth_bin = synth_binary()?;
    let synth_version = Command::new(&synth_bin)
        .arg("--version")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default();
    let root = workspace_root();
    let commit = git(&root, &["rev-parse", "HEAD"]);
    let describe = git(
        &root,
        &[
            "describe",
            "--tags",
            "--match",
            "v[0-9]*",
            "--abbrev=12",
            "--dirty",
        ],
    );
    let version = a
        .version
        .clone()
        .unwrap_or_else(|| derive_version(describe.as_deref(), commit.as_deref()));
    let commit = commit.unwrap_or_else(|| "unknown".into());
    eprintln!("target-record: {synth_version} at {commit}, version {version}");

    // The corpus, and its pin: a git checkout of its own at the gitlink.
    let files = wast_files(&a.spec_dir);
    let corpus_commit = a
        .spec_dir
        .join(".git")
        .exists()
        .then(|| git(&a.spec_dir, &["rev-parse", "HEAD"]))
        .flatten();
    let pinned = git(&root, &["ls-tree", "HEAD", "tests/spec-testsuite"])
        .and_then(|l| l.split_whitespace().nth(2).map(str::to_string));
    let corpus_problem = match (&corpus_commit, &pinned) {
        (Some(c), Some(p)) if c == p => None,
        (Some(c), Some(p)) => Some(format!("checked out {c}, pinned {p}")),
        (None, _) => Some(format!(
            "{} is not a git checkout, so its commit is unknown",
            a.spec_dir.display()
        )),
        (_, None) => Some("no tests/spec-testsuite gitlink in this checkout".to_string()),
    };
    let corpus = json!({
        "name": "WebAssembly spec testsuite (github.com/WebAssembly/testsuite), top-level .wast files",
        "files": files.len(),
        "pinned_files": SPEC_FILES,
        "commit": corpus_commit,
        "pinned_gitlink": pinned,
        "chosen_by": "the synth project; this is NOT a consumer's corpus",
        "unit": "a .wast file counts as reached when `synth compile <file> <target flags> --all-exports` exits 0 with every export compiled (the compile census's `ok` bucket)",
    });
    // The reach control: an empty corpus must not produce a passing row.
    let empty = a.work.join("empty-corpus");
    std::fs::create_dir_all(&empty).map_err(|e| e.to_string())?;
    let empty_counts = ReachCounts {
        files: wast_files(&empty).len() as u64,
        ..Default::default()
    };

    let wasm = wat::parse_str(PROBES_WAT).map_err(|e| e.to_string())?;
    let probe_in = a.work.join("probes.wasm");
    std::fs::write(&probe_in, &wasm).map_err(|e| e.to_string())?;
    let refs = references(&wasm)?;
    let ev = a.evidence.as_str();
    let targets: Vec<&Target> = TARGETS
        .iter()
        .filter(|t| a.targets.iter().any(|x| x == t.name))
        .collect();

    let mut facts: Vec<Fact> = Vec::new();
    for t in &targets {
        eprintln!("[{}]", t.name);
        // reach
        let empty_fact = reach_fact(
            t.name,
            &empty_counts,
            SPEC_FILES,
            t.reach_floor,
            FLOORS_SET_AT,
            Some(true),
            "",
            json!(null),
            ev,
        );
        let reach_control = !empty_fact.ran && !empty_fact.pass;
        let mut rc = run_reach(&files, t.flags, &a.work.join(format!("reach-{}", t.name)))?;
        rc.corpus_mismatch = corpus_problem.clone();
        eprintln!(
            "  reach: {} of {} compiled, {} panics, {} timeouts",
            rc.compiled,
            files.len(),
            rc.panics,
            rc.timeouts
        );
        facts.push(reach_fact(
            t.name,
            &rc,
            SPEC_FILES,
            t.reach_floor,
            FLOORS_SET_AT,
            Some(reach_control),
            "synth compile per corpus file, exit status + output present",
            corpus.clone(),
            ev,
        ));

        // execution_match + wcet, on the probe image.
        let elf = a.work.join(format!("probes-{}.elf", t.name));
        let mut fl: Vec<&str> = t.flags.to_vec();
        fl.extend(["--all-exports", "--emit-wcet"]);
        let (ok, text, _) = synth(&probe_in, &fl, &elf)?;
        let sidecar = read_sidecar(&elf);
        let oracle = format!(
            "{}; kiln v0.7.3 (rev fa16dc8d) reference vs unicorn {:?} (model id {} read back) on the probe module's linked self-contained ELF, booted through its Reset_Handler with the boot contract asserted",
            record::PROBE_SCOPE,
            t.cpu,
            t.cpu.model_id()
        );
        let wcet_oracle = format!(
            "{}; synth --emit-wcet (synth-wcet-v1) on the probe image; every bound must be >= the worst executed call of its function priced in Cortex-M4 TRM worst-case cycles (synth_oracle::cycles, independent of synth's table)",
            record::WCET_SCOPE
        );
        let boot = if ok {
            BootedImage::boot(&elf, t.cpu, t.fpu).map_err(|e| format!("{e:?}"))
        } else {
            Err(format!(
                "probe compile failed: {}",
                text.lines().last().unwrap_or("")
            ))
        };
        match boot {
            Err(e) => {
                eprintln!("  NOT RUN: {e}");
                facts.push(execution_fact(
                    t.name,
                    &ExecCounts::default(),
                    EXEC_FLOOR,
                    None,
                    &oracle,
                    Some(&e),
                    json!({}),
                    ev,
                ));
                let s = summarize_wcet(sidecar.as_ref(), &BTreeMap::new());
                facts.push(wcet_fact(t.name, &s, t.wcet_floor, None, &wcet_oracle, ev));
            }
            Ok(mut img) => {
                let res = sweep(&mut img, &wasm, &refs)?;
                let (ctl, ctl_detail) = execution_controls(&elf, t.cpu, t.fpu, &wasm)?;
                eprintln!(
                    "  execution_match: executed {} matched {} wrong {} inconclusive {} refused {} (trap/trap {}), controls red: {ctl}",
                    res.counts.executed,
                    res.counts.matched,
                    res.counts.wrong,
                    res.counts.inconclusive,
                    res.counts.refused,
                    res.traps
                );
                let c = &img.contract;
                facts.push(execution_fact(
                    t.name,
                    &res.counts,
                    EXEC_FLOOR,
                    Some(ctl),
                    &oracle,
                    None,
                    json!({
                        "probe_set": record::PROBE_SCOPE,
                        "cpu_model_readback": img.cpu_model_readback,
                        "boot_contract_asserted": {
                            "r11_linear_memory_base": format!("{:#010x}", c.r11_linear_memory_base),
                            "r10_linear_memory_size": format!("{:#010x}", c.r10_linear_memory_size),
                            "sp": format!("{:#010x}", c.sp),
                            "entry": format!("{} at {:#010x}", c.entry.0, c.entry.1),
                        },
                        "trap_trap": res.traps,
                        "trap_paths": res.trap_paths,
                        "controls": ctl_detail,
                    }),
                    ev,
                ));
                let s = summarize_wcet(sidecar.as_ref(), &res.max_cycles);
                for (p, e) in &res.unpriced {
                    eprintln!("  unpriced {p}: {e}");
                }
                let (wctl, wctl_detail) = wcet_control(sidecar.as_ref(), &res.max_cycles);
                eprintln!(
                    "  wcet: sidecar {} core {:?}: {} of {} bounded (floor {:?}), declines {:?}, below cost {:?}, control {wctl:?}",
                    s.sidecar,
                    s.core_class,
                    s.bounded,
                    s.functions,
                    t.wcet_floor,
                    s.declines,
                    s.below_executed
                );
                let mut f = wcet_fact(t.name, &s, t.wcet_floor, wctl, &wcet_oracle, ev);
                if let Value::Object(m) = &mut f.detail {
                    m.insert("control".into(), wctl_detail);
                    m.insert("priced_worst_cycles".into(), json!(res.max_cycles));
                    m.insert("unpriced".into(), json!(res.unpriced));
                }
                facts.push(f);
            }
        }
        facts.push(hardware_fact(t.name, ev));
    }

    let now = std::env::var("SOURCE_DATE_EPOCH")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0)
        });
    let rec = Record {
        version,
        generated_at: record::rfc3339_utc(now),
        generator_version: format!(
            "{} ({synth_version}, commit {commit})",
            env!("CARGO_PKG_VERSION")
        ),
        facts,
        not_measured: vec![
            "hardware: synth runs no silicon, so every <target>/hardware_run is ran=false; silicon rungs come from their runners (jess, gale) via pulseengine.eu".into(),
            "reach pass is a REGRESSION GATE against a floor measured at this lane's commit, not a reach threshold; no external reach target exists. Read value.fraction".into(),
            "reach corpus: the WebAssembly spec testsuite at the pinned gitlink, chosen by the synth project; no consumer corpus is measured".into(),
            "reach unit: whole .wast files with every export compiled; per-function acceptance inside a partially compiled file is not counted".into(),
            "execution_match and wcet cover only the probe set (21 call-free, memory-free, integer probes, 3024 vectors); the spec suite's directives are the spec-suite-execution job's (unicorn's permissive 'max' core), and no consumer's shipped ELF is executed".into(),
            "not executed by this record's oracle: linear-memory effects, floating point, calls, imports, multi-value results, startup data copy (the probe image has no initialised data)".into(),
            "boot: the startup is asserted to set R10/R11 to __linear_memory_base's size and address, SP to the vector table's, and to jump to a function symbol; R9 (globals) and anything beyond reaching `blx r0` are not checked".into(),
            "wcet: bounds are cross-checked against the worst executed call priced in Cortex-M4 TRM worst-case cycles over 144 vector pairs (necessary, not a soundness proof); the zero-wait-state precondition is not checked".into(),
            "targets: cortex-m4 and cortex-m7dp only (Bet B); cortex-m0plus and rv32imc are not in this record".into(),
            "attestation: this file is not attested by sigil; `wsc verify-chain` is not used as a gate (sigil#395: it passes a one-bit-flipped component)".into(),
        ],
    }
    .to_json();
    let names: Vec<&str> = targets.iter().map(|t| t.name).collect();
    record::validate_against_consumer_schema(&rec).map_err(|e| {
        format!(
            "the record is NOT schema-valid, not written:\n  {}",
            e.join("\n  ")
        )
    })?;
    record::check_complete(&rec, &names).map_err(|e| {
        format!(
            "the record is NOT complete, not written:\n  {}",
            e.join("\n  ")
        )
    })?;
    record::check_file_name(&a.out, rec["objective"].as_str().unwrap_or(""))?;
    let text = serde_json::to_string_pretty(&rec).map_err(|e| e.to_string())? + "\n";
    std::fs::write(&a.out, text).map_err(|e| format!("{}: {e}", a.out.display()))?;

    let mut code = 0;
    for f in rec["facts"].as_array().into_iter().flatten() {
        let id = f["id"].as_str().unwrap_or("?");
        let (ran, pass) = (f["ran"] == true, f["pass"] == true);
        println!(
            "FACT {id}: ran={ran} pass={pass} control_red={}",
            f["control_failed_as_expected"]
        );
        if a.require_pass.iter().any(|r| r == id) && !pass {
            eprintln!("  required fact {id} did not pass");
            code = 1;
        }
    }
    for r in &a.require_pass {
        if !rec["facts"]
            .as_array()
            .into_iter()
            .flatten()
            .any(|f| f["id"] == r.as_str())
        {
            eprintln!("  required fact {r} is not in the record");
            code = 1;
        }
    }
    println!(
        "RECORD {} schema-valid, complete, {} facts, version {}",
        a.out.display(),
        rec["facts"].as_array().map_or(0, Vec::len),
        rec["version"].as_str().unwrap_or("")
    );
    Ok(code)
}

#[cfg(test)]
mod tests {
    use super::derive_version;

    #[test]
    fn version_is_the_git_description_off_the_tag() {
        assert_eq!(derive_version(Some("v0.90.0"), Some("abc")), "0.90.0");
        assert_eq!(
            derive_version(Some("v0.90.0-53-g1a2b914186c5"), None),
            "0.90.0+53-g1a2b914186c5"
        );
        assert_eq!(
            derive_version(Some("v0.90.0-53-g1a2b914186c5-dirty"), None),
            "0.90.0+53-g1a2b914186c5-dirty"
        );
        let pkg = env!("CARGO_PKG_VERSION");
        assert_eq!(
            derive_version(None, Some("1a2b914186c5ccf2")),
            format!("{pkg}+g1a2b914186c5")
        );
        // Every form is accepted by the consumer schema's version pattern.
        let re = regex::Regex::new(r"^v?[0-9]+\.[0-9]+\.[0-9]+([-+][0-9A-Za-z.-]+)?$").unwrap();
        for v in [
            derive_version(Some("v0.90.0-53-g1a2b914186c5-dirty"), None),
            derive_version(None, Some("1a2b914186c5ccf2")),
            derive_version(None, None),
        ] {
            assert!(re.is_match(&v), "{v}");
        }
    }
}
