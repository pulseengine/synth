//! RQ-91-WRONGCODECENSUS (Refs #1741): the wrong-code census, as a test.
//!
//! One row per OPEN issue that reports wrong code (a wrong value, a wrong
//! binding or an instruction the declared target cannot execute, with exit
//! 0). The classification of the rest of the open board is recorded in
//! `docs/status/WRONG_CODE_CENSUS.md`, which this file also checks.
//!
//! Each row carries a STATUS and the evidence that produced it:
//!
//! - `Exec`: the issue's own repro is compiled by synth and every case runs on
//!   kiln and on unicorn (`synth_oracle::run_case`). LIVE iff some case
//!   disagrees, FIXED iff every case agrees, NOW-DECLINES iff synth refuses
//!   the module or drops every probed export. An inconclusive case fails the
//!   test: it is neither status.
//! - `Structural`: what the issue reports is a property of the emitted bytes
//!   or symbols that the emulator cannot run (an import call, a link-time
//!   binding, AArch64 code, an ISA extension): the test reads the object and
//!   decides the status from the property the issue names.
//! - `PyOracle`: an existing CI-wired oracle under `scripts/repro` already
//!   pins this issue's shape exactly, both ways. Its run on the census commit
//!   is the evidence; this file does not re-run it (no second harness, per
//!   the v0.92 plan's Bet A).
//!
//! The measured rows assert their status EXACTLY, both ways: a fix turns a
//! LIVE row red, and a regression turns a FIXED row red. Either is moved by
//! editing `CENSUS` and re-blessing the markdown table.
//!
//! The markdown table between the `census:begin`/`census:end` markers in
//! `docs/status/WRONG_CODE_CENSUS.md` is GENERATED from `CENSUS` and checked
//! byte-for-byte by `markdown_table_is_derived_from_census` (no engine
//! needed, so it runs in the workspace Test job).
//! `WRONG_CODE_CENSUS_BLESS=1` rewrites it.
//!
//! Run the measured rows: `cargo test -p synth-oracle --features exec --test
//! wrong_code_census -- --nocapture`.

use std::path::PathBuf;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Status {
    /// A wrong value (or binding) on the census commit.
    LiveWrong,
    /// Correct on the census commit.
    Fixed,
    /// A loud refusal on the census commit.
    NowDeclines,
    /// No runnable repro.
    CannotRepro,
}

impl Status {
    fn label(self) -> &'static str {
        match self {
            Status::LiveWrong => "LIVE-WRONG",
            Status::Fixed => "FIXED",
            Status::NowDeclines => "NOW-DECLINES",
            Status::CannotRepro => "CANNOT-REPRO",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Evidence {
    /// Executed here: kiln vs unicorn.
    Exec,
    /// Read from the emitted object here.
    Structural,
    /// An existing CI-wired oracle under `scripts/repro`, run on the census
    /// commit (not re-run by this file).
    PyOracle(&'static str),
    /// Nothing runnable; the reason. (No row uses it on the census date.)
    #[allow(dead_code)]
    None(&'static str),
}

struct Row {
    issue: u32,
    /// Backend and target as the issue states them.
    target: &'static str,
    /// The flags the evidence used.
    flags: &'static str,
    status: Status,
    evidence: Evidence,
    /// Default flags on Thumb-2 cortex-m4 (`--target cortex-m4`, no other
    /// codegen flag): the population of Bet A's zero target.
    m4_default: bool,
    /// The commit or PR that moved it, where one is known.
    note: &'static str,
}

/// When and on what the census was measured.
const MEASURED_ON: &str =
    "2026-11-20, main 3dc31524 (+ the unmerged oracle-kiln and x86objplan stack)";

const CENSUS: &[Row] = &[
    Row {
        issue: 1191,
        target: "arm cortex-m3",
        flags: "--relocatable --all-exports (a component)",
        status: Status::NowDeclines,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "components refused, f5b72988 (#1687)",
    },
    Row {
        issue: 1205,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "routed to the direct selector, 761c6922 (#1228)",
    },
    Row {
        issue: 1210,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "4a3f6080 (#1249)",
    },
    Row {
        issue: 1214,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "",
    },
    Row {
        issue: 1226,
        target: "arm cortex-m4",
        flags: "--relocatable --all-exports, .wast input",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "single-module .wast homes as .wat; a multi-module merge is refused",
    },
    Row {
        issue: 1241,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "31980043 (#1271), 6aed6daa (#1728)",
    },
    Row {
        issue: 1568,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::Fixed,
        evidence: Evidence::PyOracle("scripts/repro/npa_const_addr_matrix_1568.py"),
        m4_default: false,
        note: "162 cells: 158 equal, 0 wrong, 4 refused; 2ef015ee (#1682)",
    },
    Row {
        issue: 1604,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle("scripts/repro/npa_model_differential.py"),
        m4_default: false,
        note: "refused `npa-region-straddle (#1604)`, 2ef015ee (#1682)",
    },
    Row {
        issue: 1661,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi --safety-bounds software",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle("scripts/repro/npa_model_differential.py"),
        m4_default: false,
        note: "refused `npa-software-bounds (#1661)`, 2ef015ee (#1682)",
    },
    Row {
        issue: 1672,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle("scripts/repro/npa_model_differential.py"),
        m4_default: false,
        note: "refused `npa-data-pointer (#1672)`, 2ef015ee (#1682)",
    },
    Row {
        issue: 1676,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi; self-contained",
        status: Status::Fixed,
        evidence: Evidence::PyOracle("scripts/repro/imported_global_slots_rq91_differential.py"),
        m4_default: false,
        note: "defined globals execute equal; reading the imported global itself is refused, 0d22bafe (#1680)",
    },
    Row {
        issue: 1677,
        target: "synth-backend library (mpu.rs)",
        flags: "MPURegion::rasr()",
        status: Status::Fixed,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "6b697bcf (#1678)",
    },
    Row {
        issue: 1684,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle("scripts/repro/npa_model_differential.py"),
        m4_default: false,
        note: "refused `npa-i64-static-const (#1684)`, 2ef015ee (#1682)",
    },
    Row {
        issue: 1691,
        target: "arm cortex-m7 (reduced: cortex-m4)",
        flags: "--relocatable --all-exports",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "0185ba07 (#1694); the reporter's float attachment is not re-run",
    },
    Row {
        issue: 1696,
        target: "arm cortex-m4",
        flags: "--all-exports (default, optimized path)",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: true,
        note: "",
    },
    Row {
        issue: 1698,
        target: "arm cortex-m4",
        flags: "--relocatable --all-exports",
        status: Status::NowDeclines,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "6b3d5c2a (#1700)",
    },
    Row {
        issue: 1699,
        target: "arm cortex-m4",
        flags: "--all-exports (default, direct selector)",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: true,
        note: "",
    },
    Row {
        issue: 1710,
        target: "arm cortex-m4f/m7dp (run: cortex-m4)",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "34781a8c (#1718)",
    },
    Row {
        issue: 1711,
        target: "arm cortex-m4f/m7dp (run: cortex-m4)",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "547729fe (#1719)",
    },
    Row {
        issue: 1712,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
    },
    Row {
        issue: 1713,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "6aed6daa (#1728)",
    },
    Row {
        issue: 1714,
        target: "arm cortex-m4 + rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a155ca7f (#1725)",
    },
    Row {
        issue: 1715,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
    },
    Row {
        issue: 1716,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
    },
    Row {
        issue: 1717,
        target: "rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "c0790baa (#1727)",
    },
    Row {
        issue: 1720,
        target: "rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "265235dc (#1729)",
    },
    Row {
        issue: 1721,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
    },
    Row {
        issue: 1739,
        target: "rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "4d80d9d6 (#1748)",
    },
    Row {
        issue: 1744,
        target: "rv32i",
        flags: "-b riscv --target rv32i --relocatable",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "",
    },
    Row {
        issue: 1745,
        target: "synth-backend-aarch64 library (compile_module)",
        flags: "cortex-a53, relocatable, software bounds",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "",
    },
    Row {
        issue: 1747,
        target: "aarch64",
        flags: "-b aarch64 --relocatable",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "fix on the unmerged v092-a64below branch",
    },
    Row {
        issue: 1752,
        target: "arm cortex-m4 (also cortex-r5, aarch64)",
        flags: "--relocatable --all-exports",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "",
    },
];

/// Open issues read and classified NOT wrong-code, by class. Every open
/// issue on the census date is in exactly one of `CENSUS` or this table.
const NOT_WRONG_CODE: &[(&str, &[u32])] = &[
    (
        "loud decline / missing feature",
        &[
            380, 1145, 1229, 1230, 1231, 1254, 1267, 1301, 1426, 1441, 1447, 1448, 1673, 1703,
            1724, 1726, 1740, 1746,
        ],
    ),
    (
        "machinery / docs / tooling",
        &[
            242, 1057, 1062, 1063, 1085, 1132, 1136, 1159, 1217, 1236, 1238, 1308, 1359, 1373,
            1403, 1418, 1422, 1428, 1433, 1437, 1451, 1460, 1476, 1515, 1516, 1517, 1567, 1609,
            1613, 1704, 1723, 1731, 1738, 1741,
        ],
    ),
    ("unclear", &[1207, 1450]),
];

/// The number of open issues on the census date
/// (`gh issue list --state open --limit 300`).
const OPEN_ISSUES: usize = 86;

fn count(s: Status) -> usize {
    CENSUS.iter().filter(|r| r.status == s).count()
}

fn evidence_text(e: Evidence) -> String {
    match e {
        Evidence::Exec => "exec: kiln vs unicorn (this test)".into(),
        Evidence::Structural => {
            "structural: object bytes, symbols or library output (this test)".into()
        }
        Evidence::PyOracle(p) => format!("`{p}`"),
        Evidence::None(r) => format!("none: {r}"),
    }
}

/// The generated markdown block.
fn render() -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    writeln!(s, "Measured: {MEASURED_ON}.").unwrap();
    writeln!(s).unwrap();
    let wrong = CENSUS.len();
    let not: usize = NOT_WRONG_CODE.iter().map(|(_, v)| v.len()).sum();
    writeln!(s, "| Count | Value |").unwrap();
    writeln!(s, "|---|---|").unwrap();
    writeln!(s, "| open issues | {OPEN_ISSUES} |").unwrap();
    writeln!(s, "| wrong-code | {wrong} |").unwrap();
    for (class, v) in NOT_WRONG_CODE {
        writeln!(s, "| {class} | {} |", v.len()).unwrap();
    }
    for st in [
        Status::LiveWrong,
        Status::Fixed,
        Status::NowDeclines,
        Status::CannotRepro,
    ] {
        writeln!(s, "| wrong-code, {} | {} |", st.label(), count(st)).unwrap();
    }
    let m4 = CENSUS
        .iter()
        .filter(|r| r.m4_default && r.status == Status::LiveWrong)
        .count();
    writeln!(
        s,
        "| wrong-code, LIVE-WRONG on cortex-m4 with default flags | {m4} |"
    )
    .unwrap();
    assert_eq!(
        wrong + not,
        OPEN_ISSUES,
        "every open issue is classified once"
    );
    writeln!(s).unwrap();
    writeln!(
        s,
        "| Issue | Backend / target | Flags | Status | M4 default | Evidence | Moved by |"
    )
    .unwrap();
    writeln!(s, "|---|---|---|---|---|---|---|").unwrap();
    for r in CENSUS {
        writeln!(
            s,
            "| #{} | {} | {} | {} | {} | {} | {} |",
            r.issue,
            r.target,
            r.flags,
            r.status.label(),
            if r.m4_default { "yes" } else { "no" },
            evidence_text(r.evidence),
            r.note
        )
        .unwrap();
    }
    writeln!(s).unwrap();
    writeln!(s, "Not wrong-code (classified from the issue body):").unwrap();
    writeln!(s).unwrap();
    for (class, v) in NOT_WRONG_CODE {
        let list: Vec<String> = v.iter().map(|n| format!("#{n}")).collect();
        writeln!(s, "- {class}: {}", list.join(", ")).unwrap();
    }
    s
}

const BEGIN: &str =
    "<!-- census:begin (generated by crates/synth-oracle/tests/wrong_code_census.rs) -->\n";
const END: &str = "<!-- census:end -->";

fn md_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../docs/status/WRONG_CODE_CENSUS.md")
}

#[test]
fn markdown_table_is_derived_from_census() {
    let path = md_path();
    let md = std::fs::read_to_string(&path).expect("docs/status/WRONG_CODE_CENSUS.md exists");
    let b = md.find(BEGIN).expect("begin marker") + BEGIN.len();
    let e = md.find(END).expect("end marker");
    let want = render();
    if std::env::var_os("WRONG_CODE_CENSUS_BLESS").is_some() {
        let new = format!("{}{}{}", &md[..b], want, &md[e..]);
        std::fs::write(&path, new).unwrap();
        return;
    }
    assert_eq!(
        &md[b..e],
        want,
        "the census table in {} is not the one CENSUS generates; re-bless with \
         WRONG_CODE_CENSUS_BLESS=1",
        path.display()
    );
}

#[test]
fn census_rows_are_unique_and_disjoint() {
    let mut all: Vec<u32> = CENSUS.iter().map(|r| r.issue).collect();
    for (_, v) in NOT_WRONG_CODE {
        all.extend(v.iter());
    }
    let n = all.len();
    all.sort_unstable();
    all.dedup();
    assert_eq!(all.len(), n, "an issue is classified twice");
    assert_eq!(n, OPEN_ISSUES);
    // A measured status needs measured evidence; CANNOT-REPRO needs none.
    for r in CENSUS {
        match (r.status, r.evidence) {
            (Status::CannotRepro, Evidence::None(_)) => {}
            (Status::CannotRepro, _) | (_, Evidence::None(_)) => {
                panic!("#{}: status and evidence disagree", r.issue)
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// The measured rows. Need `--features exec` (kiln + unicorn) and the synth
// binary (`SYNTH`, or built by the harness).
// ---------------------------------------------------------------------------

#[cfg(feature = "exec")]
mod measured {
    use super::*;

    use object::{Object as _, ObjectSection as _, ObjectSymbol as _, RelocationTarget};
    use synth_oracle::compare::{EmuOutcome, RefOutcome, Verdict};
    use synth_oracle::emulate::{Cpu, EmuConfig};
    use synth_oracle::reference::Imports;
    use synth_oracle::synth::{CompileRun, compile, synth_binary};
    use synth_oracle::value::WasmValue;
    use synth_oracle::{CaseError, run_case};

    const FUEL: u64 = 1_000_000;

    struct Leg {
        name: &'static str,
        cpu: Cpu,
        flags: &'static [&'static str],
    }

    const M4_DEFAULT: Leg = Leg {
        name: "cortex-m4 default",
        cpu: Cpu::CortexM4,
        flags: &[
            "--target",
            "cortex-m4",
            "--all-exports",
            "--allow-skipped-exports",
        ],
    };
    const M4_RELOC: Leg = Leg {
        name: "cortex-m4 --relocatable",
        cpu: Cpu::CortexM4,
        flags: &[
            "--target",
            "cortex-m4",
            "--relocatable",
            "--all-exports",
            "--allow-skipped-exports",
        ],
    };
    const RV32_RELOC: Leg = Leg {
        name: "rv32imac --relocatable",
        cpu: Cpu::Rv32Imac,
        flags: &[
            "-b",
            "riscv",
            "--target",
            "riscv32imac",
            "--relocatable",
            "--all-exports",
            "--allow-skipped-exports",
        ],
    };

    /// One compiled input and the calls made on it.
    struct Probe {
        leg: Leg,
        /// The module (the reference runs this).
        wat: &'static str,
        /// When set, synth compiles this `.wast` text instead (#1226).
        wast: Option<&'static str>,
        calls: Vec<(&'static str, Vec<WasmValue>)>,
    }

    fn i(v: i32) -> WasmValue {
        WasmValue::I32(v as u32)
    }
    fn l(v: i64) -> WasmValue {
        WasmValue::I64(v as u64)
    }

    const I32S: &[i32] = &[
        0,
        1,
        2,
        3,
        5,
        7,
        9,
        100,
        -1,
        -5,
        1_000_003,
        i32::MAX,
        i32::MIN,
    ];

    /// The x values #1739 measured the #1691 fixture with. Not `I32S`: the
    /// fixture's `t_i32_loop_exit` counts up to `x + 3`, so a negative x
    /// below -3 loops for ~2^32 iterations on both engines.
    const FIXTURE_X: &[i32] = &[0, 1, 2, 5, 7, 100, -1];

    fn fixture(export: &'static str) -> Vec<(&'static str, Vec<WasmValue>)> {
        FIXTURE_X.iter().map(|&a| (export, vec![i(a)])).collect()
    }

    fn unary(export: &'static str) -> Vec<(&'static str, Vec<WasmValue>)> {
        I32S.iter().map(|&a| (export, vec![i(a)])).collect()
    }
    fn binary(export: &'static str) -> Vec<(&'static str, Vec<WasmValue>)> {
        let mut v = Vec::new();
        for &a in I32S {
            for &b in &[1, 2, 3, 4, 7, 800, -1, -5, 0] {
                v.push((export, vec![i(a), i(b)]));
            }
        }
        v
    }

    fn scratch() -> PathBuf {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("wrong-code-census-{}-{n}", std::process::id()));
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    /// Compile `src` (`.wat` or `.wast` by `ext`) with `flags`.
    fn synth(src: &str, ext: &str, flags: &[&str]) -> CompileRun {
        let d = scratch();
        let input = d.join(format!("m.{ext}"));
        std::fs::write(&input, src).unwrap();
        compile(&input, flags, &d.join("m.o")).expect("synth runs")
    }

    /// Run every probe; return the row's status and a log.
    fn exec_status(issue: u32, probes: Vec<Probe>) -> Status {
        let mut agree = 0usize;
        let mut wrong = 0usize;
        let mut declined = 0usize;
        let mut calls = 0usize;
        for p in probes {
            let wasm = wat::parse_str(p.wat).expect("probe WAT parses");
            let run = match p.wast {
                Some(w) => synth(w, "wast", p.leg.flags),
                None => synth(p.wat, "wat", p.leg.flags),
            };
            let Some(obj) = run.object else {
                eprintln!("#{issue} [{}]: synth refused: {}", p.leg.name, run.stderr);
                calls += p.calls.len();
                declined += p.calls.len();
                continue;
            };
            let cfg = EmuConfig::new(p.leg.cpu);
            for (export, args) in &p.calls {
                calls += 1;
                if obj.func(export).is_none() {
                    declined += 1;
                    continue;
                }
                let c = match run_case(&wasm, &obj, export, args, FUEL, &Imports::new(), &cfg) {
                    Ok(c) => c,
                    Err(CaseError::LinearMemory) => panic!("#{issue}: probe has a memory"),
                    Err(e) => panic!("#{issue} {export}{args:?}: harness error {e:?}"),
                };
                match &c.verdict {
                    Verdict::Agree => agree += 1,
                    Verdict::Disagree(why) => {
                        if wrong < 3 {
                            eprintln!(
                                "#{issue} [{}] {export}{args:?}: {why} (kiln {:?}, synth {:?})",
                                p.leg.name, c.reference, c.emulator
                            );
                        }
                        wrong += 1;
                    }
                    // kiln returned within its fuel and the machine code did
                    // not return within 1M instructions: non-termination,
                    // which is #1714's ARM symptom. Wrong, not inconclusive.
                    Verdict::Inconclusive(_)
                        if matches!(c.reference, RefOutcome::Values(_))
                            && c.emulator == EmuOutcome::Budget =>
                    {
                        eprintln!(
                            "#{issue} [{}] {export}{args:?}: kiln returned {:?}, synth did not return",
                            p.leg.name, c.reference
                        );
                        wrong += 1;
                    }
                    Verdict::Inconclusive(why) => {
                        panic!(
                            "#{issue} [{}] {export}{args:?}: inconclusive: {why}",
                            p.leg.name
                        )
                    }
                }
            }
        }
        eprintln!("#{issue}: {calls} calls, {agree} agree, {wrong} wrong, {declined} declined");
        assert!(calls > 0, "#{issue}: no calls");
        if wrong > 0 {
            Status::LiveWrong
        } else if declined == calls {
            Status::NowDeclines
        } else {
            assert_eq!(declined, 0, "#{issue}: a partial decline is not a status");
            Status::Fixed
        }
    }

    fn exec_probes(issue: u32) -> Vec<Probe> {
        match issue {
            1205 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module
                  (func (export "check_jam") (param i32 i32) (result i32)
                    local.get 0 local.get 1 i32.gt_s
                    if (result i32) i32.const 1 else i32.const 0 end)
                  (func (export "jam_k") (param i32 i32) (result i32)
                    local.get 0 i32.const 5 i32.gt_s
                    if (result i32) i32.const 1 else i32.const 0 end)
                  (func (export "jam_79") (param i32 i32) (result i32)
                    local.get 0 local.get 1 i32.gt_s
                    if (result i32) i32.const 7 else i32.const 9 end))"#,
                wast: None,
                calls: [binary("check_jam"), binary("jam_k"), binary("jam_79")].concat(),
            }],
            1210 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module
                  (func $dummy)
                  (func (export "as-binary-operand") (result i32)
                    (i32.mul (block (result i32) (call $dummy) (i32.const 3))
                             (block (result i32) (call $dummy) (i32.const 4))))
                  (func (export "multi") (result i32)
                    (block (call $dummy) (call $dummy) (call $dummy) (call $dummy))
                    (block (result i32) (call $dummy) (call $dummy) (call $dummy) (i32.const 7) (call $dummy))
                    (drop)
                    (block (result i32 i64 i32)
                      (call $dummy) (call $dummy) (call $dummy) (i32.const 8) (call $dummy)
                      (call $dummy) (call $dummy) (call $dummy) (i64.const 7) (call $dummy)
                      (call $dummy) (call $dummy) (call $dummy) (i32.const 9) (call $dummy))
                    (drop) (drop)))"#,
                wast: None,
                calls: vec![("as-binary-operand", vec![]), ("multi", vec![])],
            }],
            1214 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module (func (export "init-local-i64") (result i64) (local i64) (local.get 0)))"#,
                wast: None,
                calls: vec![("init-local-i64", vec![])],
            }],
            1226 => vec![Probe {
                // An i64 param body inference cannot recover (it is never
                // read): homed as i32, the i32 after it is read from r1.
                leg: M4_RELOC,
                wat: r#"(module (func (export "p") (param i64 i32) (result i32) (local.get 1)))"#,
                wast: Some(
                    r#"(module (func (export "p") (param i64 i32) (result i32) (local.get 1)))"#,
                ),
                calls: vec![
                    ("p", vec![l(0x1_0000_0001), i(9)]),
                    ("p", vec![l(-1), i(2)]),
                    ("p", vec![l(5), i(-1)]),
                ],
            }],
            1241 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module
                  (func (export "i64_local") (result i64)
                    (local i64)
                    (local.set 0 (i64.const 0x0123456789ABCDEF))
                    (i64.add (local.get 0) (i64.const 1)))
                  (func (export "bl_brif_i64") (param i32) (result i64)
                    (local i64)
                    (block
                      (br_if 0 (i32.lt_s (local.get 0) (i32.const 0)))
                      (local.set 1 (i64.const 0x1122334455667788)))
                    (local.get 1))
                  (func (export "f_brif") (result i32)
                    (local $x i64)
                    i64.const 0x100000005
                    block
                      i32.const 1
                      br_if 0
                    end
                    local.set $x
                    local.get $x
                    i64.const 32
                    i64.shr_u
                    i32.wrap_i64))"#,
                wast: None,
                calls: [
                    vec![("i64_local", vec![]), ("f_brif", vec![])],
                    unary("bl_brif_i64"),
                ]
                .concat(),
            }],
            1691 => vec![Probe {
                // The issue's own reduced fixture; its integer exports (the
                // harness refuses float signatures).
                leg: M4_RELOC,
                wat: include_str!("../../../scripts/repro/if_arm_dead_value_1691.wat"),
                wast: None,
                calls: [
                    "t_i32_then",
                    "t_i32_else",
                    "t_i32_both",
                    "t_i32_nested",
                    "t_i32_br_table",
                    "t_i32_unreachable",
                    "t_i32_return_extra",
                    "t_i32_void_target",
                    "t_i32_mismatch_then",
                    "t_i32_mismatch_else",
                    "t_i32_both_result",
                    "t_i32_loop_exit",
                    "t_i64_void_target",
                    "t_i64_beneath_i32_carried",
                ]
                .into_iter()
                .flat_map(fixture)
                .collect(),
            }],
            1710 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module (func (export "shl") (param $x i64) (param $k i32) (result i64)
                  (return (i64.shl (local.get $x) (i64.const 31)))))"#,
                wast: None,
                calls: vec![
                    ("shl", vec![l(1), i(0)]),
                    ("shl", vec![l(3), i(0)]),
                    ("shl", vec![l(0x0123_4567_89ab_cdef), i(0)]),
                    ("shl", vec![l(-1), i(5)]),
                ],
            }],
            1711 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module (func (export "sel") (param i32 i32) (result i64)
                  (select (i64.const -1) (i64.const 0x123456789abcdef0) (i32.eq (local.get 0) (local.get 1)))))"#,
                wast: None,
                calls: binary("sel"),
            }],
            1712 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module
                  (func (export "f") (param $x i32) (param $y i32) (result i32)
                    (block $outer (result i32)
                      (block $inner (result i32)
                        i32.const 10
                        local.get $x
                        i32.eqz
                        br_if $inner
                        drop
                        local.get $x
                        i32.const 0
                        i32.lt_s
                        if
                          i32.const -1
                          br $outer
                        end
                        local.get $x
                        local.get $y
                        i32.div_s
                        br $outer)
                      i32.const 100
                      i32.add)))"#,
                wast: None,
                calls: binary("f"),
            }],
            1713 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module (func (export "f") (param i64) (result i64) (local i64)
                  local.get 0 local.tee 1 local.get 1 i64.add))"#,
                wast: None,
                calls: vec![
                    ("f", vec![l(-1)]),
                    ("f", vec![l(0x1_0000_0000)]),
                    ("f", vec![l(5)]),
                ],
            }],
            1714 => vec![
                Probe {
                    leg: M4_RELOC,
                    wat: r#"(module (func (export "f") (param i64 i32) (result i32)
                      block loop local.get 1 i32.eqz br_if 1 local.get 1 i32.const 1 i32.sub
                      local.set 1 br 0 end end local.get 1))"#,
                    wast: None,
                    calls: vec![("f", vec![l(0), i(3)]), ("f", vec![l(-1), i(7)])],
                },
                Probe {
                    leg: RV32_RELOC,
                    wat: r#"(module (func (export "f") (param i64 i32) (result i32) local.get 1))"#,
                    wast: None,
                    calls: vec![
                        ("f", vec![l(0), i(2)]),
                        ("f", vec![l(5), i(-1)]),
                        ("f", vec![l(0x1_0000_0001), i(9)]),
                    ],
                },
            ],
            1715 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module (func (export "f") (param i32) (result i32)
                  local.get 0 i32.const 3 i32.div_s local.get 0 i32.const 5 i32.rem_u i32.add
                  local.get 0 i32.const 9 i32.rem_s i32.add))"#,
                wast: None,
                calls: unary("f"),
            }],
            1716 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module
                  (func (export "f") (param i32 i32) (result i32)
                    i32.const 0 if i32.const 0 return end
                    local.get 1 i32.const -1 i32.eq if i32.const 0 local.get 0 i32.sub return end
                    local.get 0 local.get 1 i32.div_s)
                  (func (export "g") (param i32 i32) (result i32)
                    block (result i32) local.get 0 local.get 1 i32.div_s local.get 1 i32.const 1
                    i32.and br_if 0 drop local.get 0 i32.const 7 i32.rem_s end))"#,
                wast: None,
                calls: [binary("f"), binary("g")].concat(),
            }],
            1717 => vec![Probe {
                leg: RV32_RELOC,
                wat: r#"(module
                  (func (export "f") (result i64) i64.const 5 i64.const 7 i64.const 2 i64.div_u i64.add)
                  (func (export "g") (result i64) i64.const 5 i64.const -7 i64.const 2 i64.div_s i64.add)
                  (func (export "h") (result i64) i64.const 5 i64.const 7 i64.const 2 i64.rem_u i64.add))"#,
                wast: None,
                calls: vec![("f", vec![]), ("g", vec![]), ("h", vec![])],
            }],
            1720 => vec![Probe {
                leg: RV32_RELOC,
                wat: r#"(module
                  (func (export "clz") (param $a i32) (result i64) local.get $a i64.extend_i32_u i64.const 0x100000000 i64.or i64.clz)
                  (func (export "ctz") (param $a i32) (result i64) local.get $a i64.extend_i32_u i64.const 0x100000000 i64.or i64.ctz)
                  (func (export "popcnt") (param $a i32) (result i64) local.get $a i64.extend_i32_u i64.const 0x100000000 i64.or i64.popcnt))"#,
                wast: None,
                calls: [unary("clz"), unary("ctz"), unary("popcnt")].concat(),
            }],
            1721 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module
                  (func (export "div_s") (param $a i32) (param $b i32) (result i64)
                    local.get $a i64.extend_i32_s i64.const 1000 i64.add
                    local.get $a local.get $b i32.div_s i64.extend_i32_s
                    i64.add)
                  (func (export "rem_u") (param $a i32) (param $b i32) (result i64)
                    local.get $a i64.extend_i32_s i64.const 1000 i64.add
                    local.get $a local.get $b i32.rem_u i64.extend_i32_u
                    i64.add))"#,
                wast: None,
                calls: [binary("div_s"), binary("rem_u")].concat(),
            }],
            1739 => vec![Probe {
                leg: RV32_RELOC,
                wat: include_str!("../../../scripts/repro/if_arm_dead_value_1691.wat"),
                wast: None,
                calls: [
                    "t_i32_void_target",
                    "t_i32_unreachable",
                    "t_i64_void_target",
                ]
                .into_iter()
                .flat_map(fixture)
                .collect(),
            }],
            n => panic!("#{n}: no exec probe"),
        }
    }

    /// The structural rows: each returns the status the issue's property
    /// gives on the emitted object.
    fn structural_status(issue: u32) -> Status {
        match issue {
            // A component: refused loudly, naming the analysis.
            1191 => {
                let r = synth(
                    "(component)",
                    "wat",
                    &["--target", "cortex-m3", "--relocatable", "--all-exports"],
                );
                if !r.status.success() && r.stderr.contains("#1191") {
                    Status::NowDeclines
                } else {
                    Status::LiveWrong
                }
            }
            // An import whose field equals an own export: refused, or the
            // import call binds to the export.
            1698 => {
                let r = synth(
                    r#"(module
                      (import "env" "get" (func $imp (result i32)))
                      (func (export "get") (result i32) i32.const 7)
                      (func (export "use_import") (result i32) call $imp))"#,
                    "wat",
                    &["--target", "cortex-m4", "--relocatable", "--all-exports"],
                );
                if r.status.success() {
                    Status::LiveWrong
                } else {
                    Status::NowDeclines
                }
            }
            // The optimized path preserves nothing across an import call:
            // the body is push / bl / pop, so `local.get 0` after the call
            // returns whatever the import left in r0.
            1696 => {
                let r = synth(
                    r#"(module
                      (import "env" "log" (func $log (param i32)))
                      (func (export "call_log") (param i32) (result i32)
                        local.get 0 call $log local.get 0))"#,
                    "wat",
                    M4_DEFAULT.flags,
                );
                let obj = r.object.expect("compiles");
                let b = obj.function_bytes("call_log").expect("call_log");
                // stmdb sp!,{r4-r12,lr}; bl <log>; ldmia.w sp!,{r4-r12,pc}
                const DEFECT: [u8; 12] = [
                    0x2d, 0xe9, 0xf0, 0x5f, 0xff, 0xf7, 0xfe, 0xff, 0xbd, 0xe8, 0xf0, 0x9f,
                ];
                if b == DEFECT {
                    Status::LiveWrong
                } else {
                    Status::Fixed
                }
            }
            // The meld dispatch fallback: an import with params is called as
            // `bl __meld_dispatch_import` with only the index in r0. No
            // argument contract exists, so any such call is the defect.
            1699 => {
                let r = synth(
                    r#"(module
                      (import "env" "g" (func $g (param i32 i32) (result i32)))
                      (func $loc (result i32) i32.const 5)
                      (func (export "f") (result i32) i32.const 3 i32.const 11 call $g call $loc i32.add))"#,
                    "wat",
                    M4_DEFAULT.flags,
                );
                let Some(obj) = r.object else {
                    return Status::NowDeclines;
                };
                let data = std::fs::read(&obj.path).unwrap();
                let f = object::File::parse(&*data).unwrap();
                if f.symbols()
                    .any(|s| s.name() == Ok("__meld_dispatch_import"))
                {
                    Status::LiveWrong
                } else {
                    Status::Fixed
                }
            }
            // rv32i: an M-extension instruction (R-type, opcode 0110011,
            // funct7 0000001) in the object of a target without M.
            1744 => {
                let r = synth(
                    r#"(module (func (export "f") (param i32 i32) (result i32)
                      local.get 0 local.get 1 i32.mul local.get 1 i32.rem_u))"#,
                    "wat",
                    &["-b", "riscv", "--target", "rv32i", "--relocatable"],
                );
                let Some(obj) = r.object else {
                    return Status::NowDeclines;
                };
                let m_ext = obj
                    .text
                    .chunks_exact(4)
                    .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
                    .any(|w| w & 0x7f == 0x33 && w >> 25 == 1);
                if m_ext {
                    Status::LiveWrong
                } else {
                    Status::Fixed
                }
            }
            // AArch64 float block: the result register v0/d0 is never
            // written (no FP data-processing instruction with Rd = 0).
            1747 => {
                let (ok, _, obj) = synth_raw(
                    r#"(module (func (export "w_f32_conv") (param i32) (result f32)
                      block (result f32)
                        block (result f32) local.get 0 f32.convert_i32_s br 1 end
                      end))"#,
                    "wat",
                    &["-b", "aarch64", "--all-exports", "--relocatable"],
                );
                if !ok {
                    return Status::NowDeclines;
                }
                let words = a64_function(&obj, "w_f32_conv");
                // FP/SIMD scalar data processing: bits 28..24 = 0b11110.
                let writes_v0 = words
                    .iter()
                    .any(|w| (w >> 24) & 0x1f == 0x1e && w & 0x1f == 0);
                if writes_v0 {
                    Status::Fixed
                } else {
                    Status::LiveWrong
                }
            }
            // ARM: `call 0` relocates against the export named `func_0`
            // (function 1) instead of function 0.
            1752 => {
                let r = synth(
                    r#"(module
                      (func $zero (result i32) i32.const 111)
                      (func $one (result i32) i32.const 222)
                      (func $caller (result i32) call $zero)
                      (export "func_0" (func $one))
                      (export "caller" (func $caller)))"#,
                    "wat",
                    M4_RELOC.flags,
                );
                let Some(obj) = r.object else {
                    return Status::NowDeclines;
                };
                let data = std::fs::read(&obj.path).unwrap();
                let f = object::File::parse(&*data).unwrap();
                let local_func0 = f
                    .symbols()
                    .find(|s| s.name() == Ok("func_0") && s.is_local())
                    .expect("local func_0")
                    .address();
                let text = f.section_by_name(".text").unwrap();
                let targets: Vec<u64> = text
                    .relocations()
                    .filter_map(|(_, rel)| match rel.target() {
                        RelocationTarget::Symbol(i) => {
                            Some(f.symbol_by_index(i).unwrap().address())
                        }
                        _ => None,
                    })
                    .collect();
                assert_eq!(targets.len(), 1, "one call relocation");
                if targets[0] == local_func0 {
                    Status::Fixed
                } else {
                    Status::LiveWrong
                }
            }
            1677 => {
                use synth_backend::{MPURegion, MPUSize};
                // CMSIS ARM_MPU_REGION_SIZE_64KB = 0x0F, _32B = 0x04.
                let size = |s: MPUSize| (MPURegion::new(0, 0, s).rasr() >> 1) & 0x1f;
                if size(MPUSize::Size64KB) == 0x0f && size(MPUSize::Size32B) == 0x04 {
                    Status::Fixed
                } else {
                    Status::LiveWrong
                }
            }
            // The published compile_module drops the zero-init fact: a
            // read-before-write local returns the caller's x1.
            1745 => {
                use synth_backend_aarch64::AArch64Backend;
                use synth_core::backend::{Backend, CompileConfig, SafetyBounds};
                use synth_core::target::TargetSpec;
                use synth_core::wasm_decoder::decode_wasm_module;
                let wasm = wat::parse_str(
                    r#"(module (func (export "f") (param i32) (result i32) (local i32) local.get 1))"#,
                )
                .unwrap();
                let module = decode_wasm_module(&wasm).unwrap();
                let cfg = CompileConfig {
                    target: TargetSpec::cortex_a53(),
                    relocatable: true,
                    safety_bounds: SafetyBounds::Software,
                    ..CompileConfig::default()
                };
                let Ok(out) = AArch64Backend::new().compile_module(&module, &cfg) else {
                    return Status::NowDeclines;
                };
                let code = &out.functions[0].code;
                // mov x0, x1 ; ret
                const DEFECT: [u8; 8] = [0xe0, 0x03, 0x01, 0xaa, 0xc0, 0x03, 0x5f, 0xd6];
                if code[..] == DEFECT {
                    Status::LiveWrong
                } else {
                    Status::Fixed
                }
            }
            n => panic!("#{n}: no structural probe"),
        }
    }

    /// `synth compile` for an output `compile` cannot parse (ELF64):
    /// returns success, stderr and the object bytes.
    fn synth_raw(src: &str, ext: &str, flags: &[&str]) -> (bool, String, Vec<u8>) {
        let d = scratch();
        let input = d.join(format!("m.{ext}"));
        let out = d.join("m.o");
        std::fs::write(&input, src).unwrap();
        let o = std::process::Command::new(synth_binary().expect("synth binary"))
            .arg("compile")
            .arg(&input)
            .args(flags)
            .arg("-o")
            .arg(&out)
            .env("RUST_LOG", "error")
            .output()
            .expect("synth runs");
        let bytes = if o.status.success() {
            std::fs::read(&out).unwrap()
        } else {
            Vec::new()
        };
        (
            o.status.success(),
            String::from_utf8_lossy(&o.stderr).into_owned(),
            bytes,
        )
    }

    fn a64_function(data: &[u8], name: &str) -> Vec<u32> {
        let f = object::File::parse(data).unwrap();
        let s = f.symbols().find(|s| s.name() == Ok(name)).expect("symbol");
        let sec = f.section_by_index(s.section_index().unwrap()).unwrap();
        let bytes = sec.data().unwrap();
        let off = (s.address() - sec.address()) as usize;
        bytes[off..off + s.size() as usize]
            .chunks_exact(4)
            .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
            .collect()
    }

    #[test]
    fn measured_rows_hold_their_status() {
        let mut measured = 0;
        let mut moved = Vec::new();
        for r in CENSUS {
            let got = match r.evidence {
                Evidence::Exec => exec_status(r.issue, exec_probes(r.issue)),
                Evidence::Structural => structural_status(r.issue),
                Evidence::PyOracle(_) | Evidence::None(_) => continue,
            };
            measured += 1;
            eprintln!("#{}: {}", r.issue, got.label());
            if got != r.status {
                moved.push(format!(
                    "#{}: recorded {}, measured {}",
                    r.issue,
                    r.status.label(),
                    got.label()
                ));
            }
        }
        assert!(moved.is_empty(), "census rows moved:\n{}", moved.join("\n"));
        let live = CENSUS
            .iter()
            .filter(|r| {
                r.status == Status::LiveWrong && !matches!(r.evidence, Evidence::PyOracle(_))
            })
            .count();
        eprintln!("WRONG-CODE CENSUS: {measured} rows measured, {live} LIVE-WRONG");
    }
}
