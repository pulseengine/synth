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
    /// Executed here on unicorn arm64 against kiln (the harness's
    /// `run_case` covers ARM and RV32 only).
    ExecA64,
    /// An existing CI-wired oracle under `scripts/repro`, run on the census
    /// commit and not re-run by this file. What this file DOES check, offline
    /// (`cited_oracles_are_wired_and_pin_the_row`): the script exists, is
    /// `# ci-status: wired`, is invoked by `.github/workflows/ci.yml`, and
    /// `needle` (the pinned result that gives the row its status: an exact
    /// `--expect` line, or the named refusal) appears in the script or in
    /// ci.yml.
    PyOracle {
        script: &'static str,
        needle: &'static str,
    },
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
    /// Further CI-wired `scripts/repro` oracles that cover legs this file
    /// does not run (checked wired, like `PyOracle`).
    also: &'static [&'static str],
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
        also: &[],
    },
    Row {
        issue: 1205,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "routed to the direct selector, 761c6922 (#1228)",
        also: &[],
    },
    Row {
        issue: 1210,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "4a3f6080 (#1249)",
        also: &[],
    },
    Row {
        issue: 1214,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "",
        also: &[],
    },
    Row {
        issue: 1226,
        target: "arm cortex-m4",
        flags: "--relocatable --all-exports, .wast input",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "single-module .wast homes as .wat; a multi-module merge is refused",
        also: &[],
    },
    Row {
        issue: 1241,
        target: "arm cortex-m4",
        flags: "--all-exports (default image)",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "31980043 (#1271), 6aed6daa (#1728)",
        also: &[],
    },
    Row {
        issue: 1568,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::Fixed,
        evidence: Evidence::PyOracle {
            script: "scripts/repro/npa_const_addr_matrix_1568.py",
            needle: "--expect ok=158,refused=4,guard=0,wrong=0",
        },
        m4_default: false,
        note: "162 cells: 158 equal, 0 wrong, 4 refused; 2ef015ee (#1682)",
        also: &[],
    },
    Row {
        issue: 1604,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle {
            script: "scripts/repro/npa_model_differential.py",
            needle: "npa-region-straddle (#1604)",
        },
        m4_default: false,
        note: "refused `npa-region-straddle (#1604)`, 2ef015ee (#1682)",
        also: &[],
    },
    Row {
        issue: 1661,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi --safety-bounds software",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle {
            script: "scripts/repro/npa_model_differential.py",
            needle: "npa-software-bounds (#1661)",
        },
        m4_default: false,
        note: "refused `npa-software-bounds (#1661)`, 2ef015ee (#1682)",
        also: &[],
    },
    Row {
        issue: 1672,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle {
            script: "scripts/repro/npa_model_differential.py",
            needle: "npa-data-pointer (#1672)",
        },
        m4_default: false,
        note: "refused `npa-data-pointer (#1672)`, 2ef015ee (#1682)",
        also: &[],
    },
    Row {
        issue: 1676,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi; self-contained",
        status: Status::Fixed,
        evidence: Evidence::PyOracle {
            script: "scripts/repro/imported_global_slots_rq91_differential.py",
            needle: "# ci-checks: emulations >= 42",
        },
        m4_default: false,
        note: "defined globals execute equal; reading the imported global itself is refused, 0d22bafe (#1680)",
        also: &[],
    },
    Row {
        issue: 1677,
        target: "synth-backend library (mpu.rs)",
        flags: "MPURegion::rasr()",
        status: Status::Fixed,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "6b697bcf (#1678)",
        also: &[],
    },
    Row {
        issue: 1684,
        target: "arm cortex-m3",
        flags: "--relocatable --native-pointer-abi",
        status: Status::NowDeclines,
        evidence: Evidence::PyOracle {
            script: "scripts/repro/npa_model_differential.py",
            needle: "npa-i64-static-const (#1684)",
        },
        m4_default: false,
        note: "refused `npa-i64-static-const (#1684)`, 2ef015ee (#1682)",
        also: &[],
    },
    Row {
        issue: 1691,
        target: "arm cortex-m7 (reduced: cortex-m4)",
        flags: "--relocatable --all-exports",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "0185ba07 (#1694); the reporter's float attachment is not re-run",
        also: &[],
    },
    Row {
        issue: 1696,
        target: "arm cortex-m4",
        flags: "--all-exports (default, optimized path), import stub",
        status: Status::LiveWrong,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "executed with an import stub that clobbers r0-r3 as AAPCS allows",
        also: &[],
    },
    Row {
        issue: 1698,
        target: "arm cortex-m4",
        flags: "--relocatable --all-exports",
        status: Status::NowDeclines,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "6b3d5c2a (#1700)",
        also: &[],
    },
    Row {
        issue: 1699,
        target: "arm cortex-m4",
        flags: "--all-exports (default, direct selector), dispatcher stub",
        status: Status::LiveWrong,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "executed with a `__meld_dispatch_import` stub reading the args from r1, r2",
        also: &[],
    },
    Row {
        issue: 1710,
        target: "arm cortex-m4f/m7dp (run: cortex-m4)",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "34781a8c (#1718)",
        also: &["scripts/repro/i64_explicit_return_1710_differential.py"],
    },
    Row {
        issue: 1711,
        target: "arm cortex-m4f/m7dp (run: cortex-m4)",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "547729fe (#1719)",
        also: &["scripts/repro/i64_select_fused_cmp_1711_differential.py"],
    },
    Row {
        issue: 1712,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
        also: &[],
    },
    Row {
        issue: 1713,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "6aed6daa (#1728)",
        also: &[],
    },
    Row {
        issue: 1714,
        target: "arm cortex-m4 + rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a155ca7f (#1725)",
        also: &[],
    },
    Row {
        issue: 1715,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
        also: &[],
    },
    Row {
        issue: 1716,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
        also: &[],
    },
    Row {
        issue: 1717,
        target: "rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "c0790baa (#1727)",
        also: &[],
    },
    Row {
        issue: 1720,
        target: "rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "265235dc (#1729)",
        also: &[],
    },
    Row {
        issue: 1721,
        target: "arm cortex-m4",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "a2649209 (#1722)",
        also: &[],
    },
    Row {
        issue: 1739,
        target: "rv32imac",
        flags: "--relocatable",
        status: Status::Fixed,
        evidence: Evidence::Exec,
        m4_default: false,
        note: "4d80d9d6 (#1748)",
        also: &[],
    },
    Row {
        issue: 1744,
        target: "rv32i",
        flags: "-b riscv --target rv32i --relocatable",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "",
        also: &[],
    },
    Row {
        issue: 1745,
        target: "synth-backend-aarch64 library (compile_module)",
        flags: "cortex-a53, relocatable, software bounds",
        status: Status::LiveWrong,
        evidence: Evidence::ExecA64,
        m4_default: false,
        note: "",
        also: &[],
    },
    Row {
        issue: 1746,
        target: "arm cortex-m4, rv32imac, aarch64",
        flags: "--relocatable --all-exports",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "an export aliasing another export's function is dropped from the symtab, exit 0",
        also: &[],
    },
    Row {
        issue: 1747,
        target: "aarch64",
        flags: "-b aarch64 --relocatable",
        status: Status::LiveWrong,
        evidence: Evidence::ExecA64,
        m4_default: false,
        note: "fix on the unmerged v092-a64below branch",
        also: &[],
    },
    Row {
        issue: 1752,
        target: "arm cortex-m4 (also cortex-r5, aarch64)",
        flags: "--relocatable --all-exports",
        status: Status::LiveWrong,
        evidence: Evidence::Structural,
        m4_default: false,
        note: "",
        also: &[],
    },
    Row {
        issue: 1754,
        target: "arm cortex-m4",
        flags: "--relocatable; and default flags when the function routes to the direct selector",
        status: Status::LiveWrong,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "filed after the first census commit; added by cold review 16",
        also: &[],
    },
    Row {
        issue: 1755,
        target: "arm cortex-m4",
        flags: "--all-exports (default, optimized path), import stub",
        status: Status::LiveWrong,
        evidence: Evidence::Exec,
        m4_default: true,
        note: "found by this census; same root as #1696",
        also: &[],
    },
];

/// Open issues read and classified NOT wrong-code, by class. Every open
/// issue on the census date is in exactly one of `CENSUS` or this table.
const NOT_WRONG_CODE: &[(&str, &[u32])] = &[
    (
        "loud decline / missing feature",
        &[
            380, 1145, 1229, 1230, 1231, 1254, 1267, 1301, 1426, 1441, 1447, 1448, 1673, 1703,
            1724, 1726, 1740,
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

/// The population: the open issues on the snapshot below. It is TYPED, not
/// fetched (a test may not reach the network), so a new issue needs a row
/// here or a place in `NOT_WRONG_CODE`. `.github/workflows/oracle-kiln.yml`
/// reds when an open issue whose title says wrong code has no row.
const SNAPSHOT: &str = "2026-11-20T00:34:42Z, `gh issue list --repo pulseengine/synth \
     --state open --limit 300`, 88 open, highest #1755";
const OPEN_ISSUES: usize = 88;

fn count(s: Status) -> usize {
    CENSUS.iter().filter(|r| r.status == s).count()
}

fn evidence_text(e: Evidence) -> String {
    match e {
        Evidence::Exec => "exec: kiln vs unicorn (this test)".into(),
        Evidence::ExecA64 => "exec: kiln vs unicorn arm64 (this test)".into(),
        Evidence::Structural => {
            "structural: object bytes, symbols or library output (this test)".into()
        }
        Evidence::PyOracle { script, needle } => format!("cited: `{script}` pins `{needle}`"),
        Evidence::None(r) => format!("none: {r}"),
    }
}

/// The generated markdown block.
fn render() -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    writeln!(s, "Measured: {MEASURED_ON}.").unwrap();
    writeln!(s).unwrap();
    writeln!(s, "Population snapshot: {SNAPSHOT}.").unwrap();
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
        "| Issue | Backend / target | Flags | Status | M4 default | Evidence | Moved by / note |"
    )
    .unwrap();
    writeln!(s, "|---|---|---|---|---|---|---|").unwrap();
    for r in CENSUS {
        let mut ev = evidence_text(r.evidence);
        for a in r.also {
            ev.push_str(&format!("; also `{a}`"));
        }
        writeln!(
            s,
            "| #{} | {} | {} | {} | {} | {} | {} |",
            r.issue,
            r.target,
            r.flags,
            r.status.label(),
            if r.m4_default { "yes" } else { "no" },
            ev,
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

/// The six cited rows assert their status through their oracle: the script
/// must be CI-wired and must pin the result the row records. A row whose
/// oracle is unwired, missing, or no longer pins the recorded result reds.
#[test]
fn cited_oracles_are_wired_and_pin_the_row() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let ci = std::fs::read_to_string(root.join(".github/workflows/ci.yml")).unwrap();
    let wired = |script: &str| -> String {
        let src =
            std::fs::read_to_string(root.join(script)).unwrap_or_else(|e| panic!("{script}: {e}"));
        assert!(
            src.lines().any(|l| l == "# ci-status: wired"),
            "{script} is not `# ci-status: wired`"
        );
        assert!(ci.contains(script), "{script} is not run by ci.yml");
        src
    };
    let mut cited = 0;
    for r in CENSUS {
        if let Evidence::PyOracle { script, needle } = r.evidence {
            let src = wired(script);
            assert!(
                src.contains(needle) || ci.contains(needle),
                "#{}: `{needle}` is pinned by neither {script} nor ci.yml",
                r.issue
            );
            // The needle names the status: a named refusal for NOW-DECLINES;
            // for FIXED, an exact zero-wrong expectation or the floor of
            // executed comparisons of an oracle that fails on any mismatch.
            let refusal = needle.contains("npa-");
            match r.status {
                Status::NowDeclines => assert!(refusal, "#{}: not a refusal needle", r.issue),
                Status::Fixed => assert!(
                    !refusal
                        && (needle.contains("wrong=0") || needle.contains("ci-checks: emulations")),
                    "#{}: a FIXED needle must pin zero wrong",
                    r.issue
                ),
                s => panic!("#{}: a cited row cannot be {}", r.issue, s.label()),
            }
            cited += 1;
        }
        for a in r.also {
            wired(a);
        }
    }
    assert_eq!(cited, 6, "cited rows moved");
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
    use synth_oracle::hosted::{HostConfig, LINMEM_UNMAPPED};
    use synth_oracle::reference::Imports;
    use synth_oracle::synth::{CompileRun, compile, synth_binary};
    use synth_oracle::value::WasmValue;
    use synth_oracle::{CaseError, run_case, run_hosted};

    const FUEL: u64 = 1_000_000;

    #[derive(Clone, Copy)]
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
        /// Host functions for the module's imports. kiln and the hosted
        /// emulator (`synth_oracle::hosted`, which links each import call
        /// to a stub by its bare field name and clobbers R0-R3 and R12 on
        /// return) are given the SAME functions, and a call agrees only when
        /// the two host-call traces are equal too.
        imports: &'static [HostImport],
        calls: Vec<(&'static str, Vec<WasmValue>)>,
    }

    /// One import, as kiln and the hosted emulator serve it.
    struct HostImport {
        module: &'static str,
        field: &'static str,
        /// How many i32 params the import takes.
        params: usize,
        /// The host function on the params in order. `None` for a void
        /// import.
        f: fn([u32; 4]) -> Option<u32>,
    }

    fn kiln_imports(imports: &[HostImport]) -> Imports {
        let mut k = Imports::new();
        for h in imports {
            let f = h.f;
            let n = h.params;
            k = k.func(h.module, h.field, move |args| {
                let mut w = [0u32; 4];
                for (slot, a) in w.iter_mut().zip(args.iter().take(n)) {
                    match a {
                        WasmValue::I32(v) => *slot = *v,
                        other => return Err(format!("non-i32 import arg {other:?}")),
                    }
                }
                Ok(f(w).map(WasmValue::I32).into_iter().collect())
            });
        }
        k
    }

    fn add2(r: [u32; 4]) -> Option<u32> {
        Some(r[0].wrapping_add(r[1]))
    }
    fn void(_: [u32; 4]) -> Option<u32> {
        None
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
                // A decline is exit 1 with a diagnostic; anything else (a
                // panic is 101) is not a status.
                assert_eq!(
                    run.status.code(),
                    Some(1),
                    "#{issue} [{}]: synth failed, not declined: {}",
                    p.leg.name,
                    run.stderr
                );
                eprintln!("#{issue} [{}]: synth refused: {}", p.leg.name, run.stderr);
                calls += p.calls.len();
                declined += p.calls.len();
                continue;
            };
            let cfg = EmuConfig::new(p.leg.cpu);
            let kiln = kiln_imports(p.imports);
            // A module with imports runs on the hosted emulator (ARM only):
            // one fresh image per call, so no state crosses calls.
            let hosted = !p.imports.is_empty();
            assert!(
                !hosted || p.leg.cpu != Cpu::Rv32Imac,
                "#{issue}: the hosted emulator is ARM only"
            );
            let host_cfg = HostConfig::new(p.leg.cpu, LINMEM_UNMAPPED);
            for (export, args) in &p.calls {
                calls += 1;
                if obj.func(export).is_none() {
                    declined += 1;
                    continue;
                }
                let c = if hosted {
                    let step: [(&str, &[WasmValue]); 1] = [(export, args.as_slice())];
                    let mut cases = match run_hosted(&wasm, &obj, &step, FUEL, &kiln, &host_cfg) {
                        Ok(c) => c,
                        Err(e) => panic!("#{issue} {export}{args:?}: harness error {e:?}"),
                    };
                    assert_eq!(cases.len(), 1, "#{issue} {export}{args:?}: one step");
                    let h = cases.remove(0);
                    (h.verdict, h.reference, h.emulator)
                } else {
                    match run_case(&wasm, &obj, export, args, FUEL, &kiln, &cfg) {
                        Ok(c) => (c.verdict, c.reference, c.emulator),
                        Err(CaseError::LinearMemory) => panic!("#{issue}: probe has a memory"),
                        Err(e) => panic!("#{issue} {export}{args:?}: harness error {e:?}"),
                    }
                };
                let (verdict, reference, emulator) = c;
                match &verdict {
                    Verdict::Agree => agree += 1,
                    Verdict::Disagree(why) => {
                        if wrong < 3 {
                            eprintln!(
                                "#{issue} [{}] {export}{args:?}: {why} (kiln {:?}, synth {:?})",
                                p.leg.name, reference, emulator
                            );
                        }
                        wrong += 1;
                    }
                    // kiln returned within its fuel and the machine code did
                    // not return within 1M instructions: non-termination,
                    // which is #1714's ARM symptom. Wrong, not inconclusive.
                    Verdict::Inconclusive(_)
                        if matches!(reference, RefOutcome::Values(_))
                            && emulator == EmuOutcome::Budget =>
                    {
                        eprintln!(
                            "#{issue} [{}] {export}{args:?}: kiln returned {:?}, synth did not return",
                            p.leg.name, reference
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
                imports: &[],
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
                imports: &[],
                calls: vec![("as-binary-operand", vec![]), ("multi", vec![])],
            }],
            1214 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module (func (export "init-local-i64") (result i64) (local i64) (local.get 0)))"#,
                wast: None,
                imports: &[],
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
                imports: &[],
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
                imports: &[],
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
                imports: &[],
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
                imports: &[],
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
                imports: &[],
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
                imports: &[],
                calls: binary("f"),
            }],
            1713 => vec![Probe {
                leg: M4_RELOC,
                wat: r#"(module (func (export "f") (param i64) (result i64) (local i64)
                  local.get 0 local.tee 1 local.get 1 i64.add))"#,
                wast: None,
                imports: &[],
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
                    imports: &[],
                    calls: vec![("f", vec![l(0), i(3)]), ("f", vec![l(-1), i(7)])],
                },
                Probe {
                    leg: RV32_RELOC,
                    wat: r#"(module (func (export "f") (param i64 i32) (result i32) local.get 1))"#,
                    wast: None,
                    imports: &[],
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
                imports: &[],
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
                imports: &[],
                calls: [binary("f"), binary("g")].concat(),
            }],
            1717 => vec![Probe {
                leg: RV32_RELOC,
                wat: r#"(module
                  (func (export "f") (result i64) i64.const 5 i64.const 7 i64.const 2 i64.div_u i64.add)
                  (func (export "g") (result i64) i64.const 5 i64.const -7 i64.const 2 i64.div_s i64.add)
                  (func (export "h") (result i64) i64.const 5 i64.const 7 i64.const 2 i64.rem_u i64.add))"#,
                wast: None,
                imports: &[],
                calls: vec![("f", vec![]), ("g", vec![]), ("h", vec![])],
            }],
            1720 => vec![Probe {
                leg: RV32_RELOC,
                wat: r#"(module
                  (func (export "clz") (param $a i32) (result i64) local.get $a i64.extend_i32_u i64.const 0x100000000 i64.or i64.clz)
                  (func (export "ctz") (param $a i32) (result i64) local.get $a i64.extend_i32_u i64.const 0x100000000 i64.or i64.ctz)
                  (func (export "popcnt") (param $a i32) (result i64) local.get $a i64.extend_i32_u i64.const 0x100000000 i64.or i64.popcnt))"#,
                wast: None,
                imports: &[],
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
                imports: &[],
                calls: [binary("div_s"), binary("rem_u")].concat(),
            }],
            1739 => vec![Probe {
                leg: RV32_RELOC,
                wat: include_str!("../../../scripts/repro/if_arm_dead_value_1691.wat"),
                wast: None,
                imports: &[],
                calls: [
                    "t_i32_void_target",
                    "t_i32_unreachable",
                    "t_i64_void_target",
                ]
                .into_iter()
                .flat_map(fixture)
                .collect(),
            }],
            // A value held across an import call. The stub is a void import
            // that clobbers R0-R3 and R12, as any AAPCS callee may.
            1696 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module
                  (import "env" "log" (func $log (param i32)))
                  (func (export "call_log") (param i32) (result i32)
                    local.get 0 call $log local.get 0))"#,
                wast: None,
                imports: &[HostImport {
                    module: "env",
                    field: "log",
                    params: 1,
                    f: void,
                }],
                calls: unary("call_log"),
            }],
            // The meld dispatch fallback: the direct selector (routed there by
            // the local call) called `__meld_dispatch_import`. The hosted
            // emulator serves no stub for that symbol, so an object that
            // still calls it is a harness error that reds this row for
            // re-measurement, never FIXED; a direct `bl g` is linked to the
            // import and judged on values and the host-call trace.
            1699 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module
                  (import "env" "g" (func $g (param i32 i32) (result i32)))
                  (func $loc (result i32) i32.const 5)
                  (func (export "f") (result i32)
                    i32.const 3 i32.const 11 call $g call $loc i32.add)
                  (func (export "h") (param i32 i32) (result i32)
                    local.get 0 local.get 1 call $g call $loc i32.add))"#,
                wast: None,
                imports: &[HostImport {
                    module: "env",
                    field: "g",
                    params: 2,
                    f: add2,
                }],
                calls: [vec![("f", vec![])], binary("h")].concat(),
            }],
            // select writes a param's home while the param is still on the
            // stack. --relocatable, and default flags once an i64 local
            // routes the function to the direct selector.
            1754 => vec![
                Probe {
                    leg: M4_RELOC,
                    wat: r#"(module (func (export "f") (param i32 i32 i32) (result i32)
                      (i32.add (local.get 0) (select (local.get 2) (local.get 0) (local.get 1)))))"#,
                    wast: None,
                    imports: &[],
                    calls: vec![
                        ("f", vec![i(5), i(1), i(7)]),
                        ("f", vec![i(5), i(0), i(7)]),
                        ("f", vec![i(1), i(2), i(3)]),
                    ],
                },
                Probe {
                    leg: M4_DEFAULT,
                    wat: r#"(module (func (export "f") (param i32 i32 i32) (result i32) (local i64)
                      (local.set 3 (i64.const 1))
                      (i32.add (local.get 0) (select (local.get 2) (local.get 0) (local.get 1)))))"#,
                    wast: None,
                    imports: &[],
                    calls: vec![
                        ("f", vec![i(5), i(1), i(7)]),
                        ("f", vec![i(5), i(0), i(7)]),
                        ("f", vec![i(1), i(2), i(3)]),
                    ],
                },
            ],
            // Optimized-path import calls never marshal their arguments.
            1755 => vec![Probe {
                leg: M4_DEFAULT,
                wat: r#"(module
                  (import "env" "add2" (func $add2 (param i32 i32) (result i32)))
                  (func (export "k") (result i32) i32.const 3 i32.const 11 call $add2)
                  (func (export "f") (param i32 i32) (result i32)
                    local.get 0 i32.const 1 i32.add
                    local.get 1 i32.const 2 i32.add
                    call $add2))"#,
                wast: None,
                imports: &[HostImport {
                    module: "env",
                    field: "add2",
                    params: 2,
                    f: add2,
                }],
                calls: [vec![("k", vec![])], binary("f")].concat(),
            }],
            n => panic!("#{n}: no exec probe"),
        }
    }

    /// The structural rows. `Ok(status)` is the status the issue's property
    /// gives; `Err` means the property could not be decided (a crash, an
    /// unexpected diagnostic, bytes that are neither the defect nor a
    /// verified fix): the row must be re-measured, and it reds.
    fn structural_status(issue: u32) -> Result<Status, String> {
        match issue {
            // A component: refused loudly, naming the analysis.
            1191 => {
                let r = synth(
                    "(component)",
                    "wat",
                    &["--target", "cortex-m3", "--relocatable", "--all-exports"],
                );
                match (r.status.success(), r.stderr.contains("#1191")) {
                    (false, true) => Ok(Status::NowDeclines),
                    (true, _) => Ok(Status::LiveWrong),
                    (false, false) => Err(format!("refused without #1191: {}", r.stderr)),
                }
            }
            // An import whose field equals an own export: refused naming
            // #1698, or the import call binds to the export.
            1698 => {
                let r = synth(
                    r#"(module
                      (import "env" "get" (func $imp (result i32)))
                      (func (export "get") (result i32) i32.const 7)
                      (func (export "use_import") (result i32) call $imp))"#,
                    "wat",
                    &["--target", "cortex-m4", "--relocatable", "--all-exports"],
                );
                match (r.status.success(), r.stderr.contains("#1698")) {
                    (false, true) => Ok(Status::NowDeclines),
                    (true, _) => Ok(Status::LiveWrong),
                    (false, false) => Err(format!("refused without #1698: {}", r.stderr)),
                }
            }
            // rv32i: an M-extension instruction (R-type, opcode 0110011,
            // funct7 0000001) in the object of a target without M, or ELF
            // e_flags claiming RVC (EF_RISCV_RVC = 1). Both halves of the
            // issue; FIXED only when neither holds.
            1744 => {
                let r = synth(
                    r#"(module (func (export "f") (param i32 i32) (result i32)
                      local.get 0 local.get 1 i32.mul local.get 1 i32.rem_u))"#,
                    "wat",
                    &["-b", "riscv", "--target", "rv32i", "--relocatable"],
                );
                let Some(obj) = r.object else {
                    return if r.stderr.contains("rv32i") || r.stderr.contains("#1744") {
                        Ok(Status::NowDeclines)
                    } else {
                        Err(format!("refused without naming the profile: {}", r.stderr))
                    };
                };
                // synth's RV32 encoder emits no compressed forms; a 16-bit
                // parcel here would desynchronise the decode below.
                let words: Vec<u32> = obj
                    .text
                    .chunks_exact(4)
                    .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
                    .collect();
                if words.iter().any(|w| w & 3 != 3) {
                    return Err("a compressed parcel in .text: decode by length".into());
                }
                let m_ext = words.iter().any(|w| w & 0x7f == 0x33 && w >> 25 == 1);
                let data = std::fs::read(&obj.path).unwrap();
                let e_flags = u32::from_le_bytes([data[36], data[37], data[38], data[39]]);
                Ok(if m_ext || e_flags & 1 == 1 {
                    Status::LiveWrong
                } else {
                    Status::Fixed
                })
            }
            // A function exported under two names: every name must be a
            // defined GLOBAL symbol, on each backend that writes relocatable
            // objects.
            1746 => {
                let wat = r#"(module (func $f (result i32) i32.const 1)
                  (export "a" (func $f)) (export "b" (func $f)))"#;
                let mut live = Vec::new();
                for flags in [
                    &["--target", "cortex-m4", "--relocatable", "--all-exports"][..],
                    &[
                        "-b",
                        "riscv",
                        "--target",
                        "riscv32imac",
                        "--relocatable",
                        "--all-exports",
                    ],
                    &["-b", "aarch64", "--relocatable", "--all-exports"],
                ] {
                    let (ok, err, data) = synth_raw(wat, "wat", flags);
                    if !ok {
                        return Err(format!("{flags:?} refused: {err}"));
                    }
                    let f = object::File::parse(&*data).unwrap();
                    for name in ["a", "b"] {
                        let defined = f
                            .symbols()
                            .any(|s| s.name() == Ok(name) && s.is_global() && !s.is_undefined());
                        if !defined {
                            live.push(format!("{} lacks `{name}`", flags[1]));
                        }
                    }
                }
                eprintln!("#1746: {live:?}");
                Ok(if live.is_empty() {
                    Status::Fixed
                } else {
                    Status::LiveWrong
                })
            }
            // AArch64 float blocks: executed. The result must land in s0/d0
            // equal to kiln's; LIVE when any shape disagrees.
            1747 => {
                let wat = r#"(module
                  (func (export "w_f32_conv") (param i32) (result f32)
                    block (result f32)
                      block (result f32) local.get 0 f32.convert_i32_s br 1 end
                    end)
                  (func (export "w_f64_if") (param i32) (result f64)
                    block (result f64)
                      local.get 0
                      if (result f64) f64.const 1.5 br 1 else f64.const 2.5 br 1 end
                    end)
                  (func (export "w_f32_ret_tail") (param i32) (result f32)
                    block (result f32)
                      block (result f32) f32.const 7.5 br 1 end
                    end
                    return
                    f32.const 9.5))"#;
                let (ok, err, obj) = synth_raw(
                    wat,
                    "wat",
                    &["-b", "aarch64", "--all-exports", "--relocatable"],
                );
                if !ok {
                    return Err(format!("refused: {err}"));
                }
                let wasm = wat::parse_str(wat).unwrap();
                let mut wrong = 0;
                for name in ["w_f32_conv", "w_f64_if", "w_f32_ret_tail"] {
                    let code = a64_function(&obj, name)?;
                    for x in [0u32, 1, 5] {
                        let want = kiln_value(&wasm, name, x)?;
                        let got = a64::run(&code, u64::from(x))?;
                        let got = match want {
                            WasmValue::F32(_) => WasmValue::F32(got.d0 as u32),
                            WasmValue::F64(_) => WasmValue::F64(got.d0),
                            _ => return Err("not a float result".into()),
                        };
                        if got != want {
                            eprintln!("#1747 {name}({x}): kiln {want:?}, synth {got:?}");
                            wrong += 1;
                        }
                    }
                }
                Ok(if wrong > 0 {
                    Status::LiveWrong
                } else {
                    Status::Fixed
                })
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
                    return Err(format!("refused: {}", r.stderr));
                };
                let data = std::fs::read(&obj.path).unwrap();
                let f = object::File::parse(&*data).unwrap();
                let local_func0 = f
                    .symbols()
                    .find(|s| s.name() == Ok("func_0") && s.is_local())
                    .ok_or("no local func_0")?
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
                if targets.len() != 1 {
                    return Err(format!("{} call relocations", targets.len()));
                }
                Ok(if targets[0] == local_func0 {
                    Status::Fixed
                } else {
                    Status::LiveWrong
                })
            }
            1677 => {
                use synth_backend::{MPURegion, MPUSize};
                // CMSIS ARM_MPU_REGION_SIZE_64KB = 0x0F, _32B = 0x04.
                let size = |s: MPUSize| (MPURegion::new(0, 0, s).rasr() >> 1) & 0x1f;
                Ok(
                    if size(MPUSize::Size64KB) == 0x0f && size(MPUSize::Size32B) == 0x04 {
                        Status::Fixed
                    } else {
                        Status::LiveWrong
                    },
                )
            }
            // The published compile_module drops per-function facts:
            // executed. Two of the issue's shapes, a value-carrying block and
            // a zero-initialised local, each run on unicorn arm64 against
            // kiln. A debug build panics on the block shape (the issue's
            // documented debug symptom of the same defect), which is LIVE.
            1745 => {
                use synth_backend_aarch64::AArch64Backend;
                use synth_core::backend::{Backend, CompileConfig, SafetyBounds};
                use synth_core::target::TargetSpec;
                use synth_core::wasm_decoder::decode_wasm_module;
                let mut wrong = 0;
                for wat in [
                    r#"(module (func (export "f") (param i32) (result i32) (block (result i32) (i32.const 7))))"#,
                    r#"(module (func (export "f") (param i32) (result i32) (local i32) local.get 1))"#,
                ] {
                    let wasm = wat::parse_str(wat).unwrap();
                    let module = decode_wasm_module(&wasm).unwrap();
                    let cfg = CompileConfig {
                        target: TargetSpec::cortex_a53(),
                        relocatable: true,
                        safety_bounds: SafetyBounds::Software,
                        ..CompileConfig::default()
                    };
                    let out = std::panic::catch_unwind(|| {
                        AArch64Backend::new().compile_module(&module, &cfg)
                    });
                    let code = match out {
                        Err(_) => {
                            eprintln!("#1745 {wat}: compile_module panicked");
                            wrong += 1;
                            continue;
                        }
                        Ok(Err(e)) => return Err(format!("compile_module refused: {e}")),
                        Ok(Ok(o)) => o.functions[0].code.clone(),
                    };
                    for x in [0u32, 1, 5] {
                        let want = kiln_value(&wasm, "f", x)?;
                        let got = WasmValue::I32(a64::run(&code, u64::from(x))?.x0 as u32);
                        if got != want {
                            eprintln!("#1745 {wat}({x}): kiln {want:?}, synth {got:?}");
                            wrong += 1;
                        }
                    }
                }
                Ok(if wrong > 0 {
                    Status::LiveWrong
                } else {
                    Status::Fixed
                })
            }
            n => panic!("#{n}: no structural probe"),
        }
    }

    /// kiln's result for `name(x)`.
    fn kiln_value(wasm: &[u8], name: &str, x: u32) -> Result<WasmValue, String> {
        let r =
            synth_oracle::reference::run(wasm, name, &[WasmValue::I32(x)], FUEL, &Imports::new())
                .map_err(|e| format!("kiln: {e:?}"))?;
        match r.outcome {
            RefOutcome::Values(v) if v.len() == 1 => Ok(v[0]),
            o => Err(format!("kiln: {o:?}")),
        }
    }

    /// A minimal AArch64 runner for the census (unicorn arm64): one
    /// function, `x0` in, returns x0 and d0. x1-x7 and d0 are POISONED first,
    /// so a result left unwritten reads back as poison, never as a lucky 0.
    mod a64 {
        use unicorn_engine::{Arch, Mode, Prot, RegisterARM64, Unicorn};

        const CODE: u64 = 0x1_0000;
        const STACK_TOP: u64 = 0x30_0000;
        const RET: u64 = 0x40_0000;
        pub const POISON_X: u64 = 0xBADC_0DE0_0000_0000;
        pub const POISON_D: u64 = 0x7FF4_DEAD_7FA0_BEEF;

        pub struct Out {
            pub x0: u64,
            pub d0: u64,
        }

        pub fn run(code: &[u8], x0: u64) -> Result<Out, String> {
            fn e(w: &'static str) -> impl Fn(unicorn_engine::uc_error) -> String {
                move |err| format!("{w}: {err:?}")
            }
            let mut u = Unicorn::new(Arch::ARM64, Mode::ARM).map_err(e("new"))?;
            let len = (code.len() as u64 + 0xFFF) & !0xFFF;
            u.mem_map(CODE, len.max(0x1000), Prot::ALL)
                .map_err(e("map code"))?;
            u.mem_write(CODE, code).map_err(e("write code"))?;
            u.mem_map(STACK_TOP - 0x2_0000, 0x2_0000, Prot::READ | Prot::WRITE)
                .map_err(e("map stack"))?;
            u.mem_map(RET, 0x1000, Prot::ALL).map_err(e("map ret"))?;
            // FPEN: let EL0/EL1 use the FP/SIMD registers.
            u.reg_write(RegisterARM64::CPACR_EL1, 3 << 20)
                .map_err(e("cpacr"))?;
            u.reg_write(RegisterARM64::X0, x0).map_err(e("x0"))?;
            let xs = [
                RegisterARM64::X1,
                RegisterARM64::X2,
                RegisterARM64::X3,
                RegisterARM64::X4,
                RegisterARM64::X5,
                RegisterARM64::X6,
                RegisterARM64::X7,
            ];
            for (k, r) in xs.into_iter().enumerate() {
                u.reg_write(r, POISON_X | k as u64).map_err(e("xn"))?;
            }
            u.reg_write(RegisterARM64::D0, POISON_D).map_err(e("d0"))?;
            u.reg_write(RegisterARM64::SP, STACK_TOP).map_err(e("sp"))?;
            u.reg_write(RegisterARM64::X30, RET).map_err(e("lr"))?;
            u.emu_start(CODE, RET, 0, 100_000).map_err(e("run"))?;
            let pc = u.reg_read(RegisterARM64::PC).map_err(e("pc"))?;
            if pc != RET {
                return Err(format!("did not return (pc {pc:#x})"));
            }
            Ok(Out {
                x0: u.reg_read(RegisterARM64::X0).map_err(e("read x0"))?,
                d0: u.reg_read(RegisterARM64::D0).map_err(e("read d0"))?,
            })
        }
    }

    /// The runner can fail: a body that writes nothing returns the poison,
    /// and one that writes the result returns it.
    #[test]
    fn a64_runner_reads_what_the_code_wrote() {
        // mov w0, #7 ; ret
        let ok = a64::run(&[0xe0, 0x00, 0x80, 0x52, 0xc0, 0x03, 0x5f, 0xd6], 0).unwrap();
        assert_eq!(ok.x0, 7);
        assert_eq!(ok.d0, a64::POISON_D, "d0 poisoned and untouched");
        // fmov s0, #1.0 ; ret
        let f = a64::run(&[0x00, 0x10, 0x2e, 0x1e, 0xc0, 0x03, 0x5f, 0xd6], 0).unwrap();
        assert_eq!(f.d0 as u32, 0x3f80_0000);
        // ret: x0 is the argument, d0 the poison.
        let none = a64::run(&[0xc0, 0x03, 0x5f, 0xd6], 9).unwrap();
        assert_eq!((none.x0, none.d0), (9, a64::POISON_D));
    }

    /// The hosted path can fail, on values AND on the host-call trace. The
    /// reference runs `wat`; synth compiles `wast` (the probe's own escape
    /// hatch), so a compiled body that differs from the reference's must
    /// measure LIVE-WRONG through the same `exec_status` the rows use.
    #[test]
    fn hosted_import_path_can_red() {
        const REF: &str = r#"(module
          (import "env" "add2" (func $add2 (param i32 i32) (result i32)))
          (func (export "f") (param i32 i32) (result i32)
            local.get 0 i32.const 1 i32.add
            local.get 1 i32.const 2 i32.add
            call $add2))"#;
        let probe = |wast: Option<&'static str>| Probe {
            leg: M4_RELOC,
            wat: REF,
            wast,
            imports: &[HostImport {
                module: "env",
                field: "add2",
                params: 2,
                f: add2,
            }],
            calls: vec![("f", vec![i(10), i(20)]), ("f", vec![i(-1), i(5)])],
        };
        // The same module: linked to the stub, every call agrees.
        assert_eq!(exec_status(9001, vec![probe(None)]), Status::Fixed);
        // A different result after the same host call: a value mismatch.
        let value = r#"(module
          (import "env" "add2" (func $add2 (param i32 i32) (result i32)))
          (func (export "f") (param i32 i32) (result i32)
            local.get 0 i32.const 1 i32.add
            local.get 1 i32.const 2 i32.add
            call $add2 i32.const 1 i32.add))"#;
        assert_eq!(exec_status(9002, vec![probe(Some(value))]), Status::LiveWrong);
        // The same result with different host-call arguments: values agree,
        // the traces do not.
        let trace = r#"(module
          (import "env" "add2" (func $add2 (param i32 i32) (result i32)))
          (func (export "f") (param i32 i32) (result i32)
            local.get 0 i32.const 2 i32.add
            local.get 1 i32.const 1 i32.add
            call $add2))"#;
        assert_eq!(exec_status(9003, vec![probe(Some(trace))]), Status::LiveWrong);
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

    /// The bytes of `name` in an AArch64 object; refused if the function
    /// carries a relocation (it would not run unlinked).
    fn a64_function(data: &[u8], name: &str) -> Result<Vec<u8>, String> {
        let f = object::File::parse(data).map_err(|e| e.to_string())?;
        let s = f
            .symbols()
            .find(|s| s.name() == Ok(name))
            .ok_or(format!("no symbol {name}"))?;
        let sec = f.section_by_index(s.section_index().unwrap()).unwrap();
        let (lo, hi) = (s.address(), s.address() + s.size());
        if sec.relocations().any(|(o, _)| o >= lo && o < hi) {
            return Err(format!("{name} carries a relocation"));
        }
        let bytes = sec.data().unwrap();
        let off = (lo - sec.address()) as usize;
        Ok(bytes[off..off + s.size() as usize].to_vec())
    }

    /// The LIVE exec rows can print FIXED: the same probes, pointed at a
    /// path that compiles them correctly (the controls the issues name),
    /// agree with kiln. Without this a row that could never agree would look
    /// like a live defect forever.
    #[test]
    fn live_exec_rows_can_flip_on_their_controls() {
        for (issue, leg) in [(1696, M4_RELOC), (1755, M4_RELOC), (1699, M4_RELOC)] {
            let probes: Vec<Probe> = exec_probes(issue)
                .into_iter()
                .map(|p| Probe { leg, ..p })
                .collect();
            assert_eq!(
                exec_status(issue, probes),
                Status::Fixed,
                "#{issue} control"
            );
        }
        // #1754 on the optimized default path (no i64 local): correct.
        let opt = exec_probes(1754)
            .into_iter()
            .take(1)
            .map(|p| Probe {
                leg: M4_DEFAULT,
                ..p
            })
            .collect();
        assert_eq!(exec_status(1754, opt), Status::Fixed, "#1754 control");
    }

    #[test]
    fn measured_rows_hold_their_status() {
        let mut moved = Vec::new();
        let mut tally = std::collections::BTreeMap::new();
        for r in CENSUS {
            let got = match r.evidence {
                Evidence::Exec => Ok(exec_status(r.issue, exec_probes(r.issue))),
                Evidence::Structural | Evidence::ExecA64 => structural_status(r.issue),
                Evidence::PyOracle { .. } | Evidence::None(_) => continue,
            };
            match got {
                Ok(got) => {
                    eprintln!("#{}: {}", r.issue, got.label());
                    *tally.entry(got).or_insert(0) += 1;
                    if got != r.status {
                        moved.push(format!(
                            "#{}: recorded {}, measured {}",
                            r.issue,
                            r.status.label(),
                            got.label()
                        ));
                    }
                }
                Err(why) => moved.push(format!("#{}: RE-MEASURE: {why}", r.issue)),
            }
        }
        assert!(moved.is_empty(), "census rows moved:\n{}", moved.join("\n"));
        let n = |s| tally.get(&s).copied().unwrap_or(0);
        let measured: usize = tally.values().sum();
        let cited = CENSUS
            .iter()
            .filter(|r| matches!(r.evidence, Evidence::PyOracle { .. }))
            .count();
        eprintln!(
            "WRONG-CODE CENSUS: {measured} rows measured: {} LIVE-WRONG, {} FIXED, {} NOW-DECLINES; {cited} rows cited",
            n(Status::LiveWrong),
            n(Status::Fixed),
            n(Status::NowDeclines)
        );
    }
}
