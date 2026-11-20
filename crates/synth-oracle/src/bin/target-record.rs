//! `target-record` — write synth's half of North Star O1 as
//! `north-star-input.O1.json` (RQ-91-TARGETRECORD, Refs #1741; consumer seam
//! pulseengine.eu#393, schema `data/north-star/input.schema.json`).
//!
//! ONE command, every number executed in this run:
//!
//! ```text
//! SYNTH=target/debug/synth cargo run -p synth-oracle --features exec \
//!     --bin target-record -- --out north-star-input.O1.json
//! ```
//!
//! Per target, four facts, never summed:
//!
//! - `reach`: every top-level `.wast` of the vendored WebAssembly spec
//!   testsuite (pinned gitlink, 257 files) compiled with `--all-exports`; a
//!   file counts when synth exits 0 with every export compiled (the compile
//!   census's `ok` bucket). The corpus was chosen by the project, not by a
//!   consumer, and the record says so.
//! - `execution_match`: the embedded probe set (`synth_oracle::probes`)
//!   compiled to the SELF-CONTAINED image, booted through its own
//!   `Reset_Handler` on the target's unicorn CPU model (Cortex-M4 / Cortex-M7,
//!   read back and asserted), every probe x vector judged against kiln.
//! - `wcet`: the `--emit-wcet` sidecar of that same compile, each bound
//!   cross-checked against the instructions its function executed.
//! - `hardware_run`: always `ran: false`. synth runs no silicon.
//!
//! Each executed fact carries a real negative control from THIS run: a planted
//! wrong reference and a planted illegal instruction (execution), a planted
//! below-execution bound (wcet), an empty corpus (reach). A control that does
//! not turn its fact red makes the fact fail.
//!
//! The output is validated against the vendored consumer schema before it is
//! written; an invalid record is an error, never a file. The process exits 0
//! when a schema-valid record was written, WHATEVER the facts say: a failing
//! fact is a measurement, not a crash. `--require-pass <id>` (repeatable)
//! turns a named fact's failure into exit 1.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::{Value, json};
use synth_oracle::compare::{EmuOutcome, RefOutcome, Verdict, verdict};
use synth_oracle::emulate::Cpu;
use synth_oracle::image::BootedImage;
use synth_oracle::probes::{AGREE_PROBES, PROBES_WAT, VECTORS};
use synth_oracle::record::{
    self, ExecCounts, Fact, ReachCounts, Record, WcetSummary, execution_fact, hardware_fact,
    not_run_fact, reach_fact, summarize_wcet, wcet_fact,
};
use synth_oracle::reference::{self, Imports};
use synth_oracle::synth::synth_binary;
use synth_oracle::value::{WasmValue, export_signature};

const FUEL: u64 = 1_000_000;
const BUDGET: usize = 1_000_000;

/// The spec testsuite's top-level `.wast` count at the pinned gitlink (the
/// same 257 the compile census pins as EXPECTED_WAST_FILES).
const SPEC_FILES: u64 = 257;

/// Executed-vector floor per linked target: every AGREE probe x every vector
/// pair (21 x 12 x 12). Set to the measured count; never lowered to make a
/// run green.
const EXEC_FLOOR: u64 = 3024;

struct Target {
    name: &'static str,
    /// Flags for the probe compile (execution + wcet). `None` = no
    /// self-contained image for this target.
    image: Option<(&'static [&'static str], Cpu, bool)>,
    /// Flags for a code-level compile when there is no image (wcet only).
    object_flags: &'static [&'static str],
    reach_flags: &'static [&'static str],
    /// Reach floor: the `ok` count MEASURED at this lane's commit (stack
    /// v092-stack2 at 7537385): cortex-m4 16, cortex-m7dp 26, cortex-m0plus 2,
    /// rv32imc 9 of 257. The m4 and m7dp figures equal the compile census's
    /// `arm` (cortex-m3) and `arm_m7dp` `ok` pins, and rv32imc equals its
    /// `riscv` (rv32imac) pin. Raised when reach rises; never lowered to make a
    /// run green.
    reach_floor: u64,
    no_image_reason: &'static str,
}

const TARGETS: &[Target] = &[
    Target {
        name: "cortex-m4",
        image: Some((&["--target", "cortex-m4"], Cpu::CortexM4, false)),
        object_flags: &[],
        reach_flags: &["--target", "cortex-m4"],
        reach_floor: 16,
        no_image_reason: "",
    },
    Target {
        name: "cortex-m7dp",
        image: Some((&["--target", "cortex-m7dp"], Cpu::CortexM7, true)),
        object_flags: &[],
        reach_flags: &["--target", "cortex-m7dp"],
        reach_floor: 26,
        no_image_reason: "",
    },
    Target {
        name: "cortex-m0plus",
        image: None,
        object_flags: &["--target", "cortex-m0plus", "--relocatable"],
        reach_flags: &["--target", "cortex-m0plus", "--relocatable"],
        reach_floor: 2,
        no_image_reason: "ARMv6-M is --relocatable only: synth builds no self-contained image for cortex-m0plus, and a code-level run does not satisfy execution_match",
    },
    Target {
        name: "rv32imc",
        image: None,
        object_flags: &["-b", "riscv", "--target", "rv32imc"],
        reach_flags: &["-b", "riscv", "--target", "rv32imc"],
        reach_floor: 9,
        no_image_reason: "synth emits a relocatable RV32 ELF plus a linker script, not a linked self-contained image, so there is no shipped image to execute",
    },
];

struct Args {
    out: PathBuf,
    spec_dir: PathBuf,
    work: PathBuf,
    version: String,
    evidence: String,
    targets: Vec<String>,
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
        version: env!("CARGO_PKG_VERSION").to_string(),
        evidence: default_evidence(),
        targets: TARGETS.iter().map(|t| t.name.to_string()).collect(),
        require_pass: Vec::new(),
    };
    let mut it = std::env::args().skip(1);
    while let Some(k) = it.next() {
        let mut v = || it.next().ok_or_else(|| format!("{k} needs a value"));
        match k.as_str() {
            "--out" => a.out = v()?.into(),
            "--spec-dir" => a.spec_dir = v()?.into(),
            "--work" => a.work = v()?.into(),
            "--version" => a.version = v()?,
            "--evidence" => a.evidence = v()?,
            "--targets" => a.targets = v()?.split(',').map(str::to_string).collect(),
            "--require-pass" => a.require_pass.push(v()?),
            "-h" | "--help" => {
                println!(
                    "target-record [--out F] [--spec-dir D] [--work D] [--version X.Y.Z] \
                     [--evidence URL] [--targets a,b] [--require-pass ID]..."
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

fn synth(input: &Path, flags: &[&str], out: &Path) -> Result<(bool, String), String> {
    let bin = synth_binary()?;
    let o = Command::new(&bin)
        .arg("compile")
        .arg(input)
        .args(flags)
        .arg("-o")
        .arg(out)
        .env("RUST_LOG", "error")
        .output()
        .map_err(|e| format!("{}: {e}", bin.display()))?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    );
    Ok((o.status.success() && out.is_file(), text))
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

/// Compile every corpus file; `(counts, per-file failures)`.
fn run_reach(files: &[PathBuf], flags: &[&str], work: &Path) -> Result<ReachCounts, String> {
    std::fs::create_dir_all(work).map_err(|e| e.to_string())?;
    let jobs = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(2)
        .clamp(1, 8);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results: std::sync::Mutex<Vec<(bool, bool)>> = std::sync::Mutex::new(Vec::new());
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
                        Ok((ok, text)) => {
                            let _ = std::fs::remove_file(&out);
                            results
                                .lock()
                                .unwrap()
                                .push((ok, text.contains("panicked")));
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
    /// function -> max instructions one call executed (judged calls only).
    max_insns: BTreeMap<String, u64>,
    traps: u64,
    /// How the emulator's traps were recognised: `udf` or `Trap_Handler`.
    trap_paths: BTreeMap<String, u64>,
    cpu_model_readback: i32,
    boot_r9_r11: [u32; 3],
}

fn sweep(
    img: &mut BootedImage,
    wasm: &[u8],
    refs: &[(String, [WasmValue; 2], RefOutcome)],
) -> Result<ExecResult, String> {
    let mut c = ExecCounts::default();
    let mut max_insns: BTreeMap<String, u64> = BTreeMap::new();
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
        let m = max_insns.entry(p.clone()).or_default();
        *m = (*m).max(run.instructions);
    }
    Ok(ExecResult {
        counts: c,
        max_insns,
        traps,
        trap_paths,
        cpu_model_readback: img.cpu_model_readback,
        boot_r9_r11: img.boot_r9_r11,
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

/// The wcet control: the sidecar with `add` replaced by a 1-cycle bound,
/// which the execution cross-check must reject.
fn wcet_control(sidecar: Option<&Value>, max_insns: &BTreeMap<String, u64>) -> bool {
    let Some(side) = sidecar else { return false };
    let mut planted = side.clone();
    let Some(funcs) = planted.get_mut("functions").and_then(Value::as_array_mut) else {
        return false;
    };
    let Some(f) = funcs
        .iter_mut()
        .find(|f| f.get("name").and_then(Value::as_str) == Some("add"))
    else {
        return false;
    };
    *f = json!({"status": "bounded", "name": "add", "cycles": 1});
    let s = summarize_wcet(Some(&planted), max_insns);
    !wcet_fact("x", &s, true, "control", "").pass
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
    let synth_bin = synth_binary()?;
    let synth_version = Command::new(&synth_bin)
        .arg("--version")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default();
    let commit = git(&workspace_root(), &["rev-parse", "HEAD"]).unwrap_or_else(|| "unknown".into());
    eprintln!("target-record: {synth_version} at {commit}");

    // The corpus, and its pin.
    let files = wast_files(&a.spec_dir);
    // Only a checkout of its own: `git -C` in a plain directory would answer
    // with the ENCLOSING repository's HEAD.
    let corpus_commit = a
        .spec_dir
        .join(".git")
        .exists()
        .then(|| git(&a.spec_dir, &["rev-parse", "HEAD"]))
        .flatten();
    let pinned = git(
        &workspace_root(),
        &["ls-tree", "HEAD", "tests/spec-testsuite"],
    )
    .and_then(|l| l.split_whitespace().nth(2).map(str::to_string));
    let corpus = json!({
        "name": "WebAssembly spec testsuite (github.com/WebAssembly/testsuite), top-level .wast files",
        "files": files.len(),
        "pinned_files": SPEC_FILES,
        "commit": corpus_commit,
        "pinned_gitlink": pinned,
        "chosen_by": "the synth project; this is NOT a consumer's corpus",
        "unit": "a .wast file counts as reached when `synth compile <file> <target flags> --all-exports` exits 0 with every export compiled (the compile census's `ok` bucket)",
    });
    let corpus_mismatch = corpus_commit.is_some() && pinned.is_some() && corpus_commit != pinned;
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

    let mut facts: Vec<Fact> = Vec::new();
    for t in TARGETS
        .iter()
        .filter(|t| a.targets.iter().any(|x| x == t.name))
    {
        eprintln!("[{}]", t.name);
        // reach
        let empty_fact = reach_fact(
            t.name,
            &empty_counts,
            SPEC_FILES,
            t.reach_floor,
            true,
            "",
            json!(null),
            ev,
        );
        let reach_control = !empty_fact.ran && !empty_fact.pass;
        let mut rc = run_reach(
            &files,
            t.reach_flags,
            &a.work.join(format!("reach-{}", t.name)),
        )?;
        if corpus_mismatch {
            rc.corpus_mismatch = Some(format!("{corpus_commit:?} != {pinned:?}"));
        }
        eprintln!(
            "  reach: {} of {} compiled, {} panics",
            rc.compiled,
            files.len(),
            rc.panics
        );
        facts.push(reach_fact(
            t.name,
            &rc,
            SPEC_FILES,
            t.reach_floor,
            reach_control,
            "synth compile per corpus file, exit status + output present",
            corpus.clone(),
            ev,
        ));

        match t.image {
            Some((flags, cpu, fpu)) => {
                let elf = a.work.join(format!("probes-{}.elf", t.name));
                let mut fl: Vec<&str> = flags.to_vec();
                fl.extend(["--all-exports", "--emit-wcet"]);
                let (ok, text) = synth(&probe_in, &fl, &elf)?;
                let sidecar = read_sidecar(&elf);
                let oracle = format!(
                    "kiln {} reference vs unicorn {:?} (model id {} read back) on the linked self-contained ELF, booted through its Reset_Handler",
                    "v0.7.3 (rev fa16dc8d)",
                    cpu,
                    cpu.model_id()
                );
                if !ok {
                    eprintln!("  probe compile failed: {text}");
                    facts.push(execution_fact(
                        t.name,
                        &ExecCounts::default(),
                        EXEC_FLOOR,
                        false,
                        &oracle,
                        true,
                        json!({"compile_error": text.lines().last().unwrap_or("")}),
                        ev,
                    ));
                    facts.push(wcet_fact(
                        t.name,
                        &summarize_wcet(None, &BTreeMap::new()),
                        false,
                        "synth --emit-wcet",
                        ev,
                    ));
                } else {
                    let mut img = BootedImage::boot(&elf, cpu, fpu)
                        .map_err(|e| format!("{}: boot: {e:?}", t.name))?;
                    let res = sweep(&mut img, &wasm, &refs)?;
                    let (ctl, ctl_detail) = execution_controls(&elf, cpu, fpu, &wasm)?;
                    eprintln!(
                        "  execution_match: executed {} matched {} wrong {} inconclusive {} refused {} (trap/trap {}), controls red: {ctl}",
                        res.counts.executed,
                        res.counts.matched,
                        res.counts.wrong,
                        res.counts.inconclusive,
                        res.counts.refused,
                        res.traps
                    );
                    facts.push(execution_fact(
                        t.name,
                        &res.counts,
                        EXEC_FLOOR,
                        ctl,
                        &oracle,
                        true,
                        json!({
                            "probe_set": "synth_oracle::probes (21 call-free, memory-free, integer probes x 144 vector pairs)",
                            "cpu_model_readback": res.cpu_model_readback,
                            "boot_r9_r10_r11": res.boot_r9_r11.iter().map(|w| format!("{w:#010x}")).collect::<Vec<_>>(),
                            "trap_trap": res.traps,
                            "trap_paths": res.trap_paths,
                            "controls": ctl_detail,
                        }),
                        ev,
                    ));
                    let s = summarize_wcet(sidecar.as_ref(), &res.max_insns);
                    let wctl = wcet_control(sidecar.as_ref(), &res.max_insns);
                    eprintln!(
                        "  wcet: sidecar {} core {:?}: {} of {} bounded, declines {:?}, control red: {wctl}",
                        s.sidecar, s.core_class, s.bounded, s.functions, s.declines
                    );
                    facts.push(wcet_fact(
                        t.name,
                        &s,
                        wctl,
                        "synth --emit-wcet (synth-wcet-v1) on the same image; every bound must be >= the instructions one executed call of its function took",
                        ev,
                    ));
                }
            }
            None => {
                facts.push(not_run_fact(
                    t.name,
                    "execution_match",
                    t.no_image_reason,
                    ev,
                ));
                // wcet: the sidecar of a code-level compile. Nothing executes,
                // so no bound can be cross-checked and none can pass.
                let obj = a.work.join(format!("probes-{}.o", t.name));
                let mut fl: Vec<&str> = t.object_flags.to_vec();
                fl.extend(["--all-exports", "--allow-skipped-exports", "--emit-wcet"]);
                let _ = synth(&probe_in, &fl, &obj)?;
                let s: WcetSummary = summarize_wcet(read_sidecar(&obj).as_ref(), &BTreeMap::new());
                eprintln!(
                    "  wcet: sidecar {} core {:?}: {} of {} bounded, declines {:?}",
                    s.sidecar, s.core_class, s.bounded, s.functions, s.declines
                );
                facts.push(wcet_fact(
                    t.name,
                    &s,
                    false,
                    "synth --emit-wcet (synth-wcet-v1) on a code-level object; no execution cross-check exists for this target",
                    ev,
                ));
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
        version: a.version.clone(),
        generated_at: record::rfc3339_utc(now),
        generator_version: format!("{} ({synth_version}, commit {commit})", env!("CARGO_PKG_VERSION")),
        facts,
        not_measured: vec![
            "hardware: synth runs no silicon, so every <target>/hardware_run is ran=false; silicon rungs come from their runners (jess, gale) via pulseengine.eu".into(),
            "reach corpus: the WebAssembly spec testsuite at the pinned gitlink, chosen by the synth project; no consumer corpus is measured".into(),
            "reach unit: whole .wast files with every export compiled; per-function acceptance inside a partially compiled file is not counted".into(),
            "execution_match: only the embedded probe set (21 call-free, memory-free, integer probes); the spec suite's directives are the spec-suite-execution job's (which runs unicorn's permissive 'max' core), and no consumer's shipped ELF is executed".into(),
            "not executed by this record's oracle: linear-memory effects, floating point, calls, imports, multi-value results".into(),
            "wcet: bounds are cross-checked only against executed instruction counts (necessary, not sufficient); the zero-wait-state precondition is not checked".into(),
            "cortex-m0plus and rv32imc: no self-contained linked image, so execution_match is ran=false".into(),
            "attestation: this file is not attested by sigil; `wsc verify-chain` is not used as a gate (sigil#395: it passes a one-bit-flipped component)".into(),
        ],
    }
    .to_json();
    record::validate_against_consumer_schema(&rec).map_err(|e| {
        format!(
            "the record is NOT schema-valid, not written:\n  {}",
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
        "RECORD {} schema-valid, {} facts",
        a.out.display(),
        rec["facts"].as_array().map_or(0, Vec::len)
    );
    Ok(code)
}
